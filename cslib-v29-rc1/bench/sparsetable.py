#!/usr/bin/env python3

class SparseTable:
    """Sparse Table for O(1) range minimum queries on an immutable array of ints."""

    def __init__(self, data: list[int]) -> None:
        assert all(isinstance(x, int) for x in data), "all elements must be int"
        n = len(data)
        if n == 0:
            self.st: list[list[int]] = []
            self.n = 0
            return
        self.n = n
        k = n.bit_length()  # ceil(log2(n)) + 1, enough levels
        self.st = [list(data)]
        for i in range(1, k):
            half = 1 << (i - 1)
            row_len = n - (1 << i) + 1
            self.st.append([min(self.st[i - 1][j], self.st[i - 1][j + half]) for j in range(row_len)])

    def query(self, l: int, r: int) -> int:
        """Return min(data[l..r]) inclusive. 0-indexed."""
        assert 0 <= l <= r < self.n
        length = r - l + 1
        k = length.bit_length() - 1  # floor(log2(length))
        return min(self.st[k][l], self.st[k][r - (1 << k) + 1])


def verify():
    import random
    for sz in range(1, 100):
        vals = [random.randint(-100, 100) for _ in range(sz)]
        st = SparseTable(vals)
        for l in range(len(vals)):
            for r in range(l, len(vals)):
                assert st.query(l, r) == min(vals[l:r+1])


if __name__ == "__main__":
    import sys
    data = sys.stdin.buffer.read().split()
    it = iter(data)
    n = int(next(it))
    q = int(next(it))
    arr = [int(next(it)) for _ in range(n)]
    st = SparseTable(arr)
    checksum = 0
    for _ in range(q):
        l = int(next(it))
        r = int(next(it))
        checksum += st.query(l, r)
    print(checksum)
