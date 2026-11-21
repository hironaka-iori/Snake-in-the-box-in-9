# Milestone 42: inductive inequalities a(n) vs a(n-1) (work in progress)

**No bound is claimed.** Status: first calibration runs.

- Facet split, rewritten in inductive form: a(n)+1 <= max_{c0+c1=k+1} g_{n-1}(c0)+g_{n-1}(c1),
  k <= floor(a(n)/n), i.e. a(n) <= 2 a(n-1) + 1 + E(c0) + E(c1) with E(c) = g_{n-1}(c) - g_{n-1}(1)
  (forest excess over snakes). Known calibration (milestone 29): 28/56/113 edges vs truth 26/50/98.
  In Q8, E(13) >= 13 (forests of 112 vertices), so this form cannot go below 223 for n = 9.
- Coupled facet split (`scripts/coupled.py`, SAT evidence, not a proof): halves A, B are induced
  linear forests with A & B = shared endpoints (crossing points), <= 2 free ends in total.
  Q5 -> Q6: at most 28 vertices (27 edges), one better than uncoupled (28 edges); truth 26.
  Q6 -> Q7: running (`data/coupled_n6_K*.log`).
