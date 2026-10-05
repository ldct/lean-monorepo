#!/usr/bin/env python3

input()
A = list(map(int, input().split()))

def ans(A):
    MODULUS = 10**9+7

    ret = 0
    cofactor = sum(A)
    for a in A:
        cofactor -= a
        ret += a*cofactor
    return ret % MODULUS

print(ans(A))
