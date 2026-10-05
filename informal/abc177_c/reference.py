#!/usr/bin/env python3

input()
A = list(map(int, input().split()))

def ans(A):
    MODULUS = 10**9+7
    ans = 0
    for i in range(len(A)):
        for j in range(i+1, len(A)):
            ans += A[i]*A[j]
    return ans % MODULUS

print(ans(A))
