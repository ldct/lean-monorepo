#!/usr/bin/env python3
"""Sqrt Tree for O(1) range minimum queries with O(n log log n) preprocessing.

Based on:
  https://cp-algorithms.com/data_structures/sqrt-tree.html
  https://github.com/ShahjalalShohag/code-library/blob/main/Data%20Structures/SQRT%20Tree.cpp

Algorithm overview:
  The array is recursively divided into blocks of size ~sqrt(segment).
  At each layer, prefix/suffix aggregates are stored within each block,
  and a "between" table stores aggregates across consecutive blocks.
  Layer 0 uses a recursive index sqrt tree for its between queries;
  deeper layers use precomputed 2D between tables.

  Block sizes are rounded to powers of 2 so that the appropriate layer
  for a query (l, r) can be identified in O(1) via XOR and bit tricks.

  Layers:  O(log log n)
  Work per layer: O(n)
  Total preprocessing: O(n log log n)
  Query: O(1)
"""


class SqrtTree:
    """Sqrt Tree for O(1) range minimum queries on an immutable array of ints."""

    def __init__(self, data: list[int]) -> None:
        n = len(data)
        self.n = n
        self.v = list(data)
        if n <= 2:
            return

        self.llg = (n - 1).bit_length()  # smallest k with 2^k >= n

        # clz[i] = bit_length(i) for i >= 1, clz[0] = 0
        sz = 1 << self.llg
        self.clz = [0] * sz
        for i in range(1, sz):
            self.clz[i] = self.clz[i >> 1] + 1

        # layers[k] = bit-length of segments at recursion depth k
        # Sequence: llg, ceil(llg/2), ceil(ceil(llg/2)/2), ... until <= 1
        self.layers: list[int] = []
        self.on_layer = [0] * (self.llg + 1)
        tllg = self.llg
        while tllg > 1:
            self.on_layer[tllg] = len(self.layers)
            self.layers.append(tllg)
            tllg = (tllg + 1) >> 1
        for i in range(self.llg - 1, -1, -1):
            self.on_layer[i] = max(self.on_layer[i], self.on_layer[i + 1])

        num_layers = len(self.layers)
        between_layers = max(0, num_layers - 1)

        bsz_log = (self.llg + 1) >> 1
        bsz = 1 << bsz_log
        self.index_sz = (n + bsz - 1) >> bsz_log

        # Extend v for the index sqrt tree (one entry per top-level block)
        self.v.extend([0] * self.index_sz)
        total = n + self.index_sz

        self.pref = [[0] * total for _ in range(num_layers)]
        self.suf = [[0] * total for _ in range(num_layers)]
        self.between = [
            [0] * ((1 << self.llg) + bsz) for _ in range(between_layers)
        ]

        self._build(0, 0, n, 0)

    # ------------------------------------------------------------------ build

    def _build_block(self, layer: int, l: int, r: int) -> None:
        """Compute prefix and suffix min arrays within block [l, r)."""
        self.pref[layer][l] = self.v[l]
        for i in range(l + 1, r):
            self.pref[layer][i] = min(self.pref[layer][i - 1], self.v[i])
        self.suf[layer][r - 1] = self.v[r - 1]
        for i in range(r - 2, l - 1, -1):
            self.suf[layer][i] = min(self.v[i], self.suf[layer][i + 1])

    def _build_between(
        self, layer: int, l_bound: int, r_bound: int, between_offs: int
    ) -> None:
        """Precompute between[i][j] = min of blocks i..j (for layer >= 1)."""
        bsz_log = (self.layers[layer] + 1) >> 1
        bcnt_log = self.layers[layer] >> 1
        bsz = 1 << bsz_log
        bcnt = (r_bound - l_bound + bsz - 1) >> bsz_log
        for i in range(bcnt):
            ans = 0
            for j in range(i, bcnt):
                add = self.suf[layer][l_bound + (j << bsz_log)]
                ans = add if i == j else min(ans, add)
                self.between[layer - 1][
                    between_offs + l_bound + (i << bcnt_log) + j
                ] = ans

    def _build_between_zero(self) -> None:
        """Build the index sqrt tree for layer-0 between queries."""
        bsz_log = (self.llg + 1) >> 1
        for i in range(self.index_sz):
            self.v[self.n + i] = self.suf[0][i << bsz_log]
        self._build(1, self.n, self.n + self.index_sz, (1 << self.llg) - self.n)

    def _build(
        self, layer: int, l_bound: int, r_bound: int, between_offs: int
    ) -> None:
        if layer >= len(self.layers):
            return
        bsz = 1 << ((self.layers[layer] + 1) >> 1)
        l = l_bound
        while l < r_bound:
            r = min(l + bsz, r_bound)
            self._build_block(layer, l, r)
            self._build(layer + 1, l, r, between_offs)
            l += bsz
        if layer == 0:
            self._build_between_zero()
        else:
            self._build_between(layer, l_bound, r_bound, between_offs)

    # ------------------------------------------------------------------ query

    def _query(self, l: int, r: int, between_offs: int, base: int) -> int:
        if l == r:
            return self.v[l]
        if l + 1 == r:
            return min(self.v[l], self.v[r])

        layer = self.on_layer[self.clz[(l - base) ^ (r - base)]]
        bsz_log = (self.layers[layer] + 1) >> 1
        bcnt_log = self.layers[layer] >> 1
        l_bound = (((l - base) >> self.layers[layer]) << self.layers[layer]) + base
        l_block = ((l - l_bound) >> bsz_log) + 1
        r_block = ((r - l_bound) >> bsz_log) - 1

        ans = self.suf[layer][l]
        if l_block <= r_block:
            if layer == 0:
                add = self._query(
                    self.n + l_block,
                    self.n + r_block,
                    (1 << self.llg) - self.n,
                    self.n,
                )
            else:
                add = self.between[layer - 1][
                    between_offs + l_bound + (l_block << bcnt_log) + r_block
                ]
            ans = min(ans, add)
        ans = min(ans, self.pref[layer][r])
        return ans

    def query(self, l: int, r: int) -> int:
        """Return min(data[l..r]) inclusive, 0-indexed."""
        assert 0 <= l <= r < self.n
        if l == r:
            return self.v[l]
        if l + 1 == r:
            return min(self.v[l], self.v[r])
        return self._query(l, r, 0, 0)


# ====================================================================== tests


def verify() -> None:
    """Exhaustive correctness check against brute-force for sizes 1..199."""
    import random

    random.seed(42)
    for sz in range(1, 200):
        vals = [random.randint(-1000, 1000) for _ in range(sz)]
        st = SqrtTree(vals)
        for l in range(len(vals)):
            for r in range(l, len(vals)):
                result = st.query(l, r)
                expected = min(vals[l : r + 1])
                assert result == expected, (
                    f"sz={sz}, l={l}, r={r}: got {result}, expected {expected}"
                )
    print("All tests passed!")


def bench() -> None:
    """Quick benchmark: build + 10^6 random queries on n=10^6."""
    import random
    import time

    n = 10**6
    random.seed(123)
    vals = [random.randint(0, 10**9) for _ in range(n)]

    t0 = time.perf_counter()
    st = SqrtTree(vals)
    t1 = time.perf_counter()
    print(f"Build  n={n}: {t1 - t0:.3f}s")

    queries = [
        (random.randint(0, n - 1), random.randint(0, n - 1)) for _ in range(10**6)
    ]
    queries = [(min(a, b), max(a, b)) for a, b in queries]

    t2 = time.perf_counter()
    s = 0
    for l, r in queries:
        s += st.query(l, r)
    t3 = time.perf_counter()
    print(f"Query  10^6 queries: {t3 - t2:.3f}s  (checksum={s})")


if __name__ == "__main__":
    import sys

    if len(sys.argv) > 1 and sys.argv[1] == "verify":
        verify()
    else:
        data = sys.stdin.buffer.read().split()
        it = iter(data)
        n = int(next(it))
        q = int(next(it))
        arr = [int(next(it)) for _ in range(n)]
        st = SqrtTree(arr)
        checksum = 0
        for _ in range(q):
            l = int(next(it))
            r = int(next(it))
            checksum += st.query(l, r)
        print(checksum)
