#!/usr/bin/env python3

import sys
from functools import reduce
from math import gcd, isqrt

def is_setwise_coprime(A):
    if len(A) == 0: return False
    cumulative_gcd = 0
    for a in A:
        cumulative_gcd = gcd(cumulative_gcd, a)
    return cumulative_gcd == 1

def is_parwise_coprime(A):
    # Generate primes up to sqrt(max(a)) by trial division.
    # This does not use a sieve.
    primes = [
        p
        for p in range(2, isqrt(max(a)) + 1)
        if all(p % d for d in range(2, isqrt(p) + 1))
    ]

    seen = set()

    for x in a:
        for p in primes:
            if p * p > x:
                break

            if x % p == 0:
                if p in seen:
                    return False

                seen.add(p)

                # Remove every copy of p from this one input.
                while x % p == 0:
                    x //= p

        # Any remaining factor greater than 1 is prime.
        if x > 1:
            if x in seen:
                return False
            seen.add(x)

    return True

def ans(A):
    if is_parwise_coprime(A):
        return "pairwise coprime"
    if is_setwise_coprime(A):
        return "setwise coprime"
    return "not coprime"

n = int(sys.stdin.buffer.readline())
a = list(map(int, sys.stdin.buffer.read().split()))
print(ans(a))