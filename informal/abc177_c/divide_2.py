#!/usr/bin/env python3

input()
A = list(map(int, input().split()))

def ans(A):
    MODULUS = 10**9+7

    ret = sum(A)**2
    for a in A:
        ret -= a*a
    ret *= 500000004
    return ret % MODULUS

print(ans(A))
