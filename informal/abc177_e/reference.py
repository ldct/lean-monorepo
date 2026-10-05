#!/usr/bin/env python3

from math import gcd

input()
A = list(map(int, input().split()))

def is_setwise_coprime(A):
    if len(A) == 0: return False
    cumulative_gcd = 0
    for a in A:
        cumulative_gcd = gcd(cumulative_gcd, a)
    return cumulative_gcd == 1

def is_parwise_coprime(A):
    for i in range(len(A)):
        for j in range(i+1, len(A)):
            if gcd(A[i], A[j]) != 1:
                return False
    return True


def ans(A):
    if is_parwise_coprime(A):
        return "pairwise coprime"
    if is_setwise_coprime(A):
        return "setwise coprime"
    return "not coprime"

print(ans(A))
