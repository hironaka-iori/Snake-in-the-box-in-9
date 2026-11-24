# Parked hard cubes (owner decision, 24 Nov 2026 00:55 UTC)

Compute goes to the remaining TOO_BIG cubes first; the hard cubes (k = 31/32 in `q6_29.txt`, plus the
diverging k = 29/30 split trees) are parked. No certificate exists for any cube below; a(9) <= 229 needs all.

## The eight cubes that cannot finish on the farm

Whole-cube CaDiCaL does not finish within a farm container's lifetime (~8 h between restarts, no
checkpointing); vertex and lookahead splits do not converge; one-level splits (`summary8.txt`) gain nothing.

| cube | k | CNF vars / clauses | evidence |
|---|---|---|---|
| 6996966996696996 | 32 | 1,117,440 / 757,513 | whole solve TIMEOUT 7,000 s: 1.46 B raw hints, 14.4 GB LRAT; tail split: no leaf built |
| 1669966996966996 | 31 | 1,089,216 / 743,416 | whole TIMEOUT 7,000 s (0.49 B hints, 5.8 GB); uncapped no-proof solve > 28,045 s (killed by restart) |
| 1669699696699669 | 31 | 1,089,216 / 743,416 | uncapped no-proof solve > 28,045 s (killed by restart); tail split: no leaf built |
| 1669966996696996 | 31 | 1,089,216 / 743,416 | tail split: no leaf built; one-level cuts UNKNOWN at 45 s |
| 0778788778878778 | 31 | 1,089,216 / 743,416 | tail split: no leaf built; one-level cuts UNKNOWN at 45 s |
| 1669699669969669 | 31 | 1,089,216 / 743,416 | tail split: no leaf built; one-level cuts UNKNOWN at 45 s |
| 1669699696696996 | 31 | 1,089,216 / 743,416 | tail split: no leaf built; one-level cuts UNKNOWN at 45 s |
| 1EE1E11EE11E1EE1 | 32 | 1,117,440 / 757,513 | tail split: no leaf built; one-level cuts UNKNOWN at 45 s |

CNF sha256: `summary8.txt` and `cubes/<hex>/hashes.txt`.

## Also parked (split trees with state kept on their machines)

Diverging (todo grew faster than leaves were built): 1669966996966969, 1be4e41be41b1be4, 19e3e61ce61c19e3,
1669699696699696, 06b9b946b94646b9, 19e6e619e61919e6, 07787887b44b4bb4, 035e7ca17ca1835e, 1669969696966969,
0669699696696996 (k = 30, t8, parked 24 Nov 17:55 UTC: depth 7, no leaf solved in 6 h),
0778788678878778 (k = 30, t32, parked 24 Nov 21:25 UTC: depth 6, 60 todo, none done in 6.5 h),
16696996833c3cc3 (k = 30, T13/t13r, parked 24 Nov 23:27 UTC: depth 7, 63 todo, none done in 3.7 h).
Failed at --max-depth 12: 06b1b14eb14e4eb1 (k = 30, T0/w15, 11 leaves done, one leaf still too big at depth 12).
A share is relaunched past a parked cube with `tail_d8.py run ... --skip A,A,...` (9ef29b22d).
Converging when parked (resume first): 1669969699666996, 1669969696996966, 16698778a55a7887,
037c7c837c83837c, 1669699687787887, 06b5b94ab94a46b5 (split again at 2 leaves left).
No hard cube is running.
