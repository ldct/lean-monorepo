#!/usr/bin/env python3

import math

class Sieve:
    def __init__(self, n=10**7+100):
        self.N = n

        s = [-1] * n
        for i in range(2, int(n**0.5)+1):
            if s[i] != -1: continue
            for j in range(i, n, i):
                if j > i: s[j] = i
        self.s = s

        self.PRIMES = self.primes()
        # print(len(self.PRIMES))

    def primes(self):
        return [i for i, e in enumerate(self.s) if e == -1 and i >= 2]

    def fastfactorize(self, n, exclude_duplicates=False):
        assert(n <= self.N)

        ret = []

        while self.s[n] != -1:
            p = self.s[n]
            ret += [p]
            if exclude_duplicates:
                while n % p == 0:
                    n = n // p
            else:
                n = n // self.s[n]

        if n > 1:
            ret += [n]

        return ret

    def fastfactorize_counter(self, n):
        assert(n <= self.N)

        ret = Counter()

        while self.s[n] != -1:
            p = self.s[n]
            ret[p] += 1
            n = n // self.s[n]

        if n > 1:
            ret[n] += 1

        return ret

    def isprime(self, n):
        if n < self.N:
            return self.s[n] == -1
        for p in self.PRIMES:
            if p*p > n:
                return True
            if n % p == 0:
                return False

    def factorize(self, n):
        if n < self.N:
            return self.fastfactorize(n)

        for p in self.PRIMES:
            if p*p > n:
                break
            if n % p == 0:
                return [p] + self.factorize(n // p)

        return [n]

sieve = Sieve()

input()
A = list(map(int, input().split()))

def is_setwise_coprime(A):
    if len(A) == 0: return False
    cumulative_gcd = 0
    for a in A:
        cumulative_gcd = math.gcd(cumulative_gcd, a)
    return cumulative_gcd == 1

def is_parwise_coprime(A):
    seen_primes = set()
    for a in A:
        for p in sieve.fastfactorize(a, exclude_duplicates=True):
            if p in seen_primes:
                return False
            seen_primes.add(p)
    return True


def ans(A):
    if is_parwise_coprime(A):
        return "pairwise coprime"
    if is_setwise_coprime(A):
        return "setwise coprime"
    return "not coprime"

print(ans(A))
