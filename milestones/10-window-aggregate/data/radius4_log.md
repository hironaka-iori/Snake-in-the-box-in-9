# Radius-4 automaton runs (local, 18–19 Oct 2026)

Edge bound ≈ 9214/(35+μ) − 2 (exact constant fixed by the Lean potential).

| run | L | k | K | radius | final mean | rounds | oracle time | bound |
|---|---|---|---|---|---|---|---|---|
| E1 | 6 | 4 | 5 | 4 | 10/3 | 39 | 114 s | 239 (same as radius 3) |
| E1-K8 | 6 | 4 | 8 | 4 | 7/2 | 31 | ~70 s | 238 |
| E2 | 7 | 5 | 5 | 4 | 42/11 ≈ 3.818 | 170 | 2861 s | ≈236 |
| E4 | 6 | 5 | 8 | 4 | **4** | 136 | 5334 s | ≈234 (final cycle (4,4,4), no lumping) |
| E5 | 6 | 5 | 8 | 5 | running | | | |

Observation: with K=5 the limiting cycles are dominated by the lumped symbol 6 (α ≥ 6), so the
cap K, not the radius, binds; raising K recovers the lost mean (k=4: 10/3 → 7/2).

E4's limiting cycle is the constant count 4 with no lumped symbol, so neither K nor the symbol
resolution binds any more: a (4,4,4,4,4) five-centre window is feasible at radius 4 with six
directions of memory. Next lever: radius 5 (same 78,732 states, slower oracle).
