# Milestone 39: lifting dimension 8 to a(9) (facet split, induced linear forests of Q8)

Run of 19 November 2026 on one 4-core machine. **No new bound on a(9) is claimed.** The
reduction theorem below is machine-checked; its Q8 premise is not. Everything about the Q8
premise is solver or enumeration evidence and is labelled as such.

## Summary

1. **Reduction, Lean-checked.** `Dim8Lift.snake_le_of_noPit` (core Lean 4.35, no mathlib;
   axioms `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`) states:
   if no induced linear forest of Q8 with at most 13 paths has L vertices, then every snake of
   Q9 has at most 2L - 3 edges (2 <= L <= 116).
   - Corollaries: `upper_229_of_noPit` (L = 116), `upper_227_of_noPit` (L = 115),
     `upper_225_of_noPit` (L = 114) and `upper_223_of_noPit` (L = 113).
   - It does **not** use the Lean cap 231: the proof cuts a prefix of 2L - 2 edges, so the
     least-used coordinate is crossed at most 25 times.
   - The premise `NoPit 13 L 64` is the semantics of milestone 29's level-encoded CNF, without
     its auxiliary variables.
2. **Where the route bottoms out.**
   - The best known forests have g8(13) = 112 (eight P7 plus four P14). Even if that is exact,
     the route gives 223 at best (221-223, depending on forests with an exact path count).
     Nothing near 220 is reachable this way.
   - Proved before this milestone (milestone 29, SAT, not certified): g8(13) <= 121.
3. **Q7 validation (solver evidence).** g7(8) = 56: no induced linear forest of Q7 with at most
   8 paths has 57 vertices.
   - This was open: milestone 29 reported "unknown after 2400 s".
   - It was settled by 2,161 cubes, all UNSAT, 1,655 s in total and at most 5.4 s each.
4. **Q8, level 115 (worth 229; solver evidence, partial).** All 21 completed sample cubes are
   UNSAT; four were stopped by hand, none came out SAT. The per-cube time grows steeply with the size of the fixed copy (table below).
   - Extrapolated cost of the full level: about 4-5 x 10^5 core-seconds of solving, which is
     110-140 core-hours, or 1-1.5 days on these 4 cores.
   - Levels 114 / 113 / 112 use the same 2,161 cubes, but each is harder; a sample is running.
5. **Certification.**
   - Done: the reduction (machine-checked).
   - Missing, in Lean:
     - the cube CNF bridge (a `Pit` gives a satisfying assignment of the cube CNF);
     - the B8 symmetry transport;
     - the verified orbit cover;
     - the LRAT replay of each cube.
   - Sizes are estimated below; the bulk is about 120-300 G LRAT hints for level 115.

## 1. The reduction (`lean/`)

Cut Q9 along coordinate i. The vertices of a snake with bit i = b form an induced linear forest
of Q8 whose paths are the snake's runs in that facet. The proof in `lean/Dim8Lift.lean`
(parts `Lift1`-`Lift5`) goes as follows.

- Take a snake with m >= 2L - 2 edges and keep its prefix of exactly 2L - 2 edges
  (`takePrefix`).
- Every step flips exactly one of the 9 bits (`sum_dif`). So some coordinate i is crossed at most
  floor(230/9) = 25 times (`exists_dir`).
- One facet holds at least L of the 2L - 1 prefix vertices. Keep its first L vertices: the
  prefix up to index j1 (`exists_hit`).
- Their projection S to Q8 (delete bit i; `Bits.lean`, all bit facts by `decide` over Fin 512)
  satisfies all of the following:
  - **degree <= 2:** a Q8 neighbour inside the facet is the previous or next snake vertex
    (`NBR`, `deg_ok`);
  - **levels:** the level ℓ is the distance to the nearer end of the run. Every vertex with two
    neighbours in S has a neighbour of smaller level (`lvl_ok`), and ℓ <= (L - 1)/2 <= 57 <= 64
    (`lv_bound`);
  - **endpoint sum** = 2 (#runs) <= 26. This is the telescoping count of facet exits and
    entries: exits - entries = [start in facet] - 1, and exits + entries <= 25 (`tele`,
    `ends_ok`);
  - **cardinality** L, by reindexing sums along the injective projection (`sm_reindex`,
    `card_ok`).

Build: `bash lean/build.sh`. It takes about 80 s; most of it is `Bits.lean` (`decide` over about
40,000 cases). The output ends with the three `#print axioms` lines quoted above. `Snake9Core.lean`
is the definition block of `work/final_lean/Snake9.lean` (`Vertex`, `Adj`, `Snake`, `takePrefix`),
copied verbatim. Linking with the audited 4.35 stack only needs the import switched to the
ported module of the same names.

## 2. What dimension-8 facts give

The value g8(c) is the largest induced linear forest of Q8 with at most c paths. Only c <= 13
matters, and the target is a(9) <= 2 g8(13) - 1:

| statement on Q8 | a(9) <= | status |
|---|---|---|
| g8(13) <= 121 | 241 | SAT-proved in milestone 29 (via c = 14), not certified |
| g8(13) <= 115 (`NoPit 13 116 64`) | **229** | sample all UNSAT; full run pending |
| g8(13) <= 114 | 227 | sample running |
| g8(13) <= 113 | 225 | not started |
| g8(13) <= 112 (the plateau conjecture) | 223 | not started; route floor |

Lower bounds come from milestone 29's annealing: g8(c) >= 112 for 8 <= c <= 16.

- The two-cut variant (Q7 quarters) is dead: g7(13) >= 61, which gives 246.
- LP and flag-algebra relaxations cannot prove g8(13) < 115.33 (milestone 32, concavity barrier).
- Any relaxation whose constraints see few vertices at a time cannot reach 220 either:
  `scripts/sdp_ceiling.py` gives an explicit locally consistent configuration.
- So exact search is the only way to settle g8(13).

## 3. Cube-and-conquer by the largest subcube copy

### Orbit enumeration (`scripts/enumk.c`, `scripts/enum6.c`)

Induced linear forests up to the hyperoctahedral group:

| cube | vertices | orbits | raw sets |
|---|---|---|---|
| Q4 | 8 | 8 | 922 |
| Q5 | >= 15 | 35 | 54,604 |
| Q6 | >= 29 | **2,161** | |
| Q6 | >= 30 | 222 | |
| Q6 | >= 31 | 24 | |

- The 2,161 Q6 orbits split by size as 1,939 / 198 / 18 / 6 at 29 / 30 / 31 / 32 vertices.
- Q6 orbits are generated from Q5 halves. A Q6 forest with >= 29 vertices has a half with >= 15
  vertices in every coordinate. For each of the 35 Q5 orbits the other half is extended
  (187,002 pairs), then canonicalised by brute force over B6 (46,080 elements).
- Cross-check: a direct brute-force enumeration for >= 31 vertices gives the same 24 orbits.
- Files: `data/q5_15.txt`, `data/q6_29.txt` (size, pieces, 64-bit mask).

### Cube CNF (`scripts/dimacs29.py`, `scripts/cubes.py`)

The CNF is milestone 29's encoding: degree <= 2, endpoint indicators with sum <= 2c, no 4-cycles
and no induced 6-cycles, levels with D = 2^(n-2), and cardinality >= L. Symmetry breaking is
replaced by the cube:

- Split Q_n = Q6 x Q_(n-6). By the counting, some copy has >= ceil(L / 2^(n-6)) vertices.
- Choose the largest 6-subcube over **all** choices of 6 coordinates (`--allmax`). Move it to
  copy 0 and normalise it by B6, so it equals one of the representatives.
- Every 6-subcube then has at most |A| vertices. This is WLOG and gives a 3x speed-up on the
  first Q8 cube (446 s -> 137 s).

### Q7, c = 8, L = 57

All 2,161 cubes are UNSAT (`data/q7_c8_L57_cubes.jsonl`): median 0.7 s, maximum 5.4 s, 1,655 s
in total on 3 jobs. With the known 56-vertex forests this gives **g7(8) = 56** (solver evidence).

The Q5-copy split (35 cubes, Q7 = Q5 x Q2) was much worse: several cubes were unknown after
300 s. Fixing half of the cube is what makes it easy.

### Q8, c = 13, L = 116 (level 115)

Stratified sample (`data/q8_c13_L116_sample.jsonl`, 4 jobs on 4 cores, CaDiCaL 2.1.3):

| fixed copy size | representatives | sampled | seconds per cube (all UNSAT) |
|---|---|---|---|
| 29 | 1,939 | 16 | 35, 62, 66, 90, 97, 98, 112, 112, 123, 129, 132, 135, 138, 142, 209, 221 |
| 30 | 198 | 5 | 269, 571, 603, 663; one stopped at 2,660 |
| 31 | 18 | 3 | 2,179; two stopped at 2,200-2,300 |
| 32 | 6 | 1 | not measured (stopped) |

- Hardness is driven by the size of the fixed copy, not by its symmetry. The size-29..31
  representatives have automorphism groups of order 1-4.
- The six size-32 representatives have stabilisers of order 16 to 23,040, so lex-leader
  breaking under Stab(A) would help exactly there.
- Estimate for the whole level, solving only:
  - 1,939 x ~110 s ≈ 2.1 x 10^5 core-seconds;
  - 198 x ~700 s ≈ 1.4 x 10^5;
  - 24 x ≥ 3,000 s ≈ 0.7-1.5 x 10^5;
  - **total about 4-5 x 10^5 core-seconds, 110-140 core-hours.**
  - Times were measured with 4 jobs on 4 cores; a single job runs about 1.3-1.5 times faster.
- Adaptive literal splitting (`scripts/split.py`) of the 2,179 s cube: 60 s leaves, branching on
  the outside vertices next to path ends of A. After 3,000 CPU-s, 21 leaves were UNSAT and 18
  were still open, so it costs at least 1.5-2 times the monolithic solve
  (`data/q8_L116_split_rep2154_partial.jsonl`). Splitting is for bounding certificate size, not
  for speed.

## 4. Certification path and sizes

The pieces and their status:

1. **Reduction.** Done: `snake_le_of_noPit`, Lean-checked, standard axioms.
2. **Cube bridge** (to write). The CNF must be a Lean definition (as for the window
   certificates) with a theorem: from `Pit 13 L 64 S ℓ` with copy 0 = A and all 6-subcubes
   <= |A|, a satisfying assignment exists. The assignment is:
   - the selection, pair, `two`, `any`, `e0`, `e1` and `d1` variables, read off S;
   - levels o(u,j) = [ℓ u >= j] with the `a` variables;
   - the sequential-counter auxiliaries, read off the prefix counts;
   - the 4-cycle and 6-cycle clauses, which follow from degree <= 2 and levels (on a cycle, a
     vertex of least level has no smaller neighbour).

   Then `LratV3.unsat_of_raw` and a kernel replay per cube close each cube. The existing checker
   kinds suffice; only the bridge and the CNF generator are new.
3. **Symmetry transport** (to write, about 300 lines). Coordinate permutations and translations
   of Q8 map a `Pit` to a `Pit` (sum reindexing by a bijection of [0,256)). A largest 6-subcube
   exists and can be moved to copy 0 of coordinates (6,7).
4. **Verified cover** (to write; certificates are small). Every Q6 set A with >= 29 vertices,
   degree <= 2 and a level function on A is B6-equivalent to one of the 2,161 representatives.
   - Two levels, each certified by one CNF UNSAT plus stored group elements checked by `decide`:
     1. Q5 completeness: one CNF with 54,604 blocking clauses of 32 literals.
     2. Per Q5 representative, the completeness of its extension list: 35 CNFs, 187,002
        blocking clauses in all.
   - Then each listed (half, extension) pair maps to its Q6 representative by a stored element
     of B6: 187,002 x 64 bit operations under `decide`.
   - The cover is thus checked, not trusted. The enumerators only produce the lists.
5. **Cube certificates**:
   - LRAT rate measured on a Q7 cube: 1.23 M hints for a 1.9 s solve, about 0.6 M hints per
     solver-second, untrimmed.
   - Level 115 at 4-5 x 10^5 solver-seconds: **about 250-300 G hints untrimmed**. If trimming
     halves it as on the window certificates, about 120-150 G.
   - For comparison, 231 took 41.5 G and 230 about 80 G.
   - Kernel cost at milestone 36's rate (about 0.23 ms per hint): roughly 8,000-20,000 Lean
     CPU-hours.
   - Cubes above about 100 s exceed the 60 M-hint cap of one certificate. They are split by
     `split.py` into 60 s leaves (at most about 36 M hints each), and the cover lemma for a split
     is a literal case split.
   - Count: about 1,700 single cubes plus about 450 cubes split into, say, 10-50 leaves each:
     **about 10^4 certificates**.

The bound 229 from this route would be independent of the K7 window machinery. It would cost
roughly 2-4 times the 230 farm in Lean CPU, versus 1,000-4,000 G hints for 229 by the K7 share
route (milestone 38). Each further level (227, 225, 223) is harder by a factor still being
measured.

## 5. The owner's questions 2(a) and 2(b) (moved to milestone 41 by the coordinator)

These were measured before the scope change:

- **SDP and moment relaxations.** A relaxation whose constraints each involve fewer than d
  vertices accepts the point mass of any set that is locally snake-like: degree <= 2, no cycle on
  <= d vertices, endpoint identity Σ x(2 - deg) = 2. Explicit sets
  (`scripts/sdp_ceiling.py`, `data/sdp_ceiling.json`): 2^(n-4) disjoint induced 8-cycles minus
  one vertex, 16 disjoint 14-cycles minus one vertex, and 8 disjoint 26-cycles minus one vertex.
  Their values bound the relaxation from below:

  | constraint support d | value at least (edges) |
  |---|---|
  | d < 8 | 254 |
  | d < 14 | 222 |
  | d < 26 | 206 |

  - Rough count of B9-orbits of d-subsets, C(512,d)/|B9|: 6 x 10^8 for d = 8 and 4 x 10^18 for
    d = 14.
  - So an SDP below 222 needs constraints on at least 14 points, which is far out of reach.
- **Exhaustive search in Q9.** Knuth's estimator on the tree of snakes from vertex 0, with
  directions introduced in order and a reachable-free-vertex prune: about 6 x 10^40 nodes for
  target 222 vertices, against 2 x 10^22 for Q8 at target 100 (`scripts/knuth.c`,
  `data/knuth_raw.txt`). That is about 10^18 times a Q8 search.

## Files

| file | content |
|---|---|
| `lean/*.lean`, `lean/build.sh` | the Lean reduction (core Lean 4.35) |
| `scripts/dimacs29.py` | milestone 29 CNF to DIMACS, with a fixed copy, `--allmax`, `--D` |
| `scripts/cubes.py` | cube runner (resumable; `SHARD=s/N`, `STRIDE`, `DIMACS_EXTRA`) |
| `scripts/split.py` | adaptive literal splitting of one cube |
| `scripts/enumk.c`, `scripts/enum6.c`, `scripts/ext7.c` | orbit enumeration; extension counts |
| `scripts/lf.py` | a lazy-cut encoder (not used: without symmetry breaking it is far slower) |
| `scripts/sdp_ceiling.py`, `scripts/knuth.c` | the question 2 estimates |
| `data/q5_15.txt`, `data/q6_29.txt`, `data/q6_30.txt`, `data/q4_8.txt` | orbit representatives |
| `data/q7_c8_L57_cubes.jsonl` | the Q7 plateau run |
| `data/q8_c13_L116_sample.jsonl`, `data/q8_sample_reps.txt` | the Q8 level-115 sample |

## Worker command (level 115, for farm machines)

On a machine with CaDiCaL 2.1.3 on PATH and `pip install python-sat`, in a checkout of this
branch:

```bash
cd milestones/39-dim8-lift/scripts
SHARD=$S/$N DIMACS_EXTRA=--allmax nohup python3 cubes.py 8 13 116 6 ../data/q6_29.txt ~/q8L116 20000 4 > ~/q8L116.log 2>&1 &
```

- Here S = 0..N-1 is the worker's share.
- Results go to `~/q8L116/results.jsonl`, one JSON line per representative.
- Representatives are processed largest first; the run is resumable.
- Memory is about 0.5 GB per job.
