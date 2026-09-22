#!/usr/bin/env python3
"""Integer-only finite certificate for the accompanying Lagarias proof.

No third-party packages, floating-point arithmetic, or transcendental
library functions are used in any assertion. Python 3.10+ suffices.
An interval (lo, hi) represents [lo / Q, hi / Q].
"""
from __future__ import annotations
from math import isqrt
from time import perf_counter

if not __debug__:
    raise RuntimeError("Run without -O/-OO: assertions are the certificate.")

BITS = 128
Q = 1 << BITS
TERMS = 48
PRIME_CAP = 1_100_000
SMALL_LIMIT = 55_440
LOG_LIMIT = 1_000_000


def ceildiv(a: int, b: int) -> int:
    assert b > 0
    return -((-a) // b)


def unit_log(a: int, b: int) -> tuple[int, int]:
    """Enclose log(a/b), for 1 <= a/b <= 2, by a finite series."""
    assert 0 < b <= a <= 2 * b
    if a == b:
        return (0, 0)
    znum, zden = a - b, a + b
    z = Q * znum // zden
    z2 = Q * znum * znum // (zden * zden)
    term, total = z, 0
    for j in range(TERMS):
        total += term // (2 * j + 1)
        term = term * z2 // Q
    lo = 2 * total
    return (lo, lo + 8 * TERMS + 8)


LN2 = unit_log(2, 1)


def lograt(a: int, b: int = 1) -> tuple[int, int]:
    """Enclose log(a/b) for arbitrary positive integers a, b."""
    assert a > 0 and b > 0
    k = a.bit_length() - b.bit_length()
    if (a < (b << k)) if k >= 0 else ((a << (-k)) < b):
        k -= 1
    if k >= 0:
        u, v = a, b << k
    else:
        u, v = a << (-k), b
    lo, hi = unit_log(u, v)
    if k >= 0:
        return (lo + k * LN2[0], hi + k * LN2[1])
    return (lo + k * LN2[1], hi + k * LN2[0])


def logiv(x: tuple[int, int]) -> tuple[int, int]:
    assert 0 < x[0] <= x[1]
    return (lograt(x[0], Q)[0], lograt(x[1], Q)[1])


def add(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
    return (x[0] + y[0], x[1] + y[1])


def divpos(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
    assert 0 < x[0] <= x[1] and 0 < y[0] <= y[1]
    return (Q * x[0] // y[1], ceildiv(Q * x[1], y[0]))


def gamma_interval() -> tuple[int, int]:
    # 1/(2(m+1)) < H_m - log(m) - gamma < 1/(2m).
    m = 10_000
    hlo = sum(Q // k for k in range(1, m + 1))
    hhi = sum(ceildiv(Q, k) for k in range(1, m + 1))
    lm = lograt(m)
    return (hlo - lm[1] - ceildiv(Q, 2 * m),
            hhi - lm[0] - Q // (2 * (m + 1)))


def primes_to(n: int) -> list[int]:
    sieve = bytearray(b'\x01') * (n + 1)
    sieve[0:2] = b'\x00\x00'
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            count = (n - p * p) // p + 1
            sieve[p * p:n + 1:p] = b'\x00' * count
    return [p for p in range(2, n + 1) if sieve[p]]


def decimal_lower(a: int, digits: int = 12) -> str:
    """Downward decimal display of a/Q (not used for certification)."""
    d = 10 ** digits
    v = a * d // Q
    sign = '-' if v < 0 else ''
    v = abs(v)
    return f'{sign}{v // d}.{v % d:0{digits}d}'


def small_check() -> tuple[int, int]:
    sigma = [0] * (SMALL_LIMIT + 1)
    for d in range(1, SMALL_LIMIT + 1):
        for n in range(d, SMALL_LIMIT + 1, d):
            sigma[n] += d
    h = (0, 0)
    minimum, argmin = None, None
    for n in range(1, SMALL_LIMIT + 1):
        h = add(h, (Q // n, ceildiv(Q, n)))
        if n == 1:
            assert sigma[n] == 1 and h == (Q, Q)
            continue
        # sigma > H; compare log(sigma-H) < H + log(log(H)).
        assert sigma[n] * Q > h[1]
        lhs_hi = lograt(sigma[n] * Q - h[0], Q)[1]
        rhs_lo = h[0] + logiv(logiv(h))[0]
        margin = rhs_lo - lhs_hi
        assert margin > 0, ('small range', n)
        if minimum is None or margin < minimum:
            minimum, argmin = margin, n
    assert minimum is not None and argmin is not None
    return minimum, argmin


def ca_check(gamma: tuple[int, int]) -> dict:
    primes = primes_to(PRIME_CAP)
    lp = {p: lograt(p) for p in primes}
    cut = divpos(lograt(PRIME_CAP + 1, PRIME_CAP), lograt(PRIME_CAP))
    # Event: [epsilon lower, epsilon upper, prime, new exponent,
    #         logarithmic gain lower, logarithmic gain upper].
    events = []
    for p in primes:
        k, s = 1, p  # s = p + ... + p^k
        while True:
            gain = lograt(s + 1, s)
            eps = divpos(gain, lp[p])
            if eps[1] < cut[0]:
                break
            assert eps[0] > cut[1], ('cutoff overlap', p, k)
            events.append((eps[0], eps[1], p, k, gain[0], gain[1]))
            k += 1
            s = p * (s + 1)
    events.sort(key=lambda e: e[0], reverse=True)
    for a, b in zip(events, events[1:]):
        assert a[0] > b[1], ('event overlap', a[2:4], b[2:4])

    exponents = {}
    cost, benefit = (0, 0), (0, 0)
    small_n = 1
    started = False
    minimum = None
    minimum_info = None
    checked = 0
    initial = []
    for index, ev in enumerate(events, 1):
        _, _, p, k, rlo, rhi = ev
        assert exponents.get(p, 0) + 1 == k
        exponents[p] = k
        cost = add(cost, lp[p])
        benefit = add(benefit, (rlo, rhi))
        if small_n is not None:
            small_n *= p
            if len(initial) < 10:
                initial.append(small_n)
            if small_n == SMALL_LIMIT:
                started = True
            elif small_n > SMALL_LIMIT:
                assert started
                small_n = None
        if started:
            bound_lo = gamma[0] + logiv(logiv(cost))[0]
            margin = bound_lo - benefit[1]
            assert margin > 0, ('CA inequality', index, p, k)
            checked += 1
            if minimum is None or margin < minimum:
                minimum = margin
                minimum_info = (index, p, k, cost[0])
        if cost[0] > LOG_LIMIT * Q:
            assert started and minimum is not None
            return dict(primes=len(primes), events=len(events),
                        processed=index, checked=checked,
                        minimum=minimum, minimum_info=minimum_info,
                        final_cost=cost, final_event=(p, k), initial=initial)
        assert cost[1] <= LOG_LIMIT * Q, 'threshold overlap'
    raise AssertionError('Increase PRIME_CAP: logarithmic threshold not reached')


def main() -> None:
    start = perf_counter()
    # Taylor tail after TERMS terms is smaller than one unit 1/Q.
    assert 9 * Q < 4 * (2 * TERMS + 1) * 3 ** (2 * TERMS + 1)
    gamma = gamma_interval()
    assert gamma[0] > 0 and 50 * gamma[1] < 29 * Q
    assert 3 * LN2[0] > 2 * Q and 10 * LN2[1] < 7 * Q
    # Combined with 3.14 < pi < 22/7, these give log(4pi)>2.53,
    # log(2pi)<2, and hence the zero-sum constant is <1/20.
    assert 100 * lograt(314, 25)[0] > 253 * Q
    assert lograt(44, 7)[1] < 2 * Q
    assert lograt(1_000_000)[0] > 13 * Q
    print('Gamma enclosure:', decimal_lower(gamma[0], 15),
          '< gamma <', decimal_lower(gamma[1] + Q // 10**15 + 1, 15))
    m, n = small_check()
    print('Small range: 2..55440, all strict; equality checked at 1.')
    print('Small-range minimum certified log margin:', decimal_lower(m),
          'at n =', n)
    data = ca_check(gamma)
    print('Sieved primes:', data['primes'])
    print('Strictly ordered events above cutoff:', data['events'])
    print('Events processed:', data['processed'])
    print('CA endpoints checked from 55440:', data['checked'])
    print('Initial endpoints:', data['initial'])
    print('Final event (prime, exponent):', data['final_event'])
    print('Final log N lower bound:', decimal_lower(data['final_cost'][0], 6))
    print('Minimum certified CA log margin:', decimal_lower(data['minimum']))
    idx, p, k, cost = data['minimum_info']
    print('Minimum at event:', idx, 'prime:', p, 'exponent:', k,
          'log N lower bound:', decimal_lower(cost, 6))
    print('CERTIFICATE PASSED')
    print('Elapsed seconds (informational only):', round(perf_counter() - start, 2))


if __name__ == '__main__':
    main()
