#!/usr/bin/env python3
"""Exact count of directed snakes by length in Q_n (small n), starting at 0 and scaled by 2^n."""
import sys, math
n = int(sys.argv[1]); NV = 1 << n
cnt = [0]*NV; occ = [False]*NV; C = {}
def dfs(e, L):
    C[L] = C.get(L, 0) + 1
    for k in range(n):
        y = e ^ (1 << k)
        if occ[y] or cnt[y] != 1: continue
        occ[y] = True
        for j in range(n): cnt[y ^ (1 << j)] += 1
        dfs(y, L+1)
        for j in range(n): cnt[y ^ (1 << j)] -= 1
        occ[y] = False
occ[0] = True
for j in range(n): cnt[1 << j] += 1
dfs(0, 0)
for L in sorted(C): print(L, f"{math.log(C[L]*NV):.6f}", C[L]*NV)
