# Milestone 39: lifting dimension 8 to a(9) (facet split, induced linear forests of Q8)

Run of 19 November 2026 on one 4-core machine. **No new bound on a(9) is claimed.** The
reduction theorem below is machine-checked; its Q8 premise is not. Everything about the Q8
premise is solver or enumeration evidence and is labelled as such.

## Summary

Status at 21:30 UTC. **No new bound on a(9) is claimed.** The whole route below is a
machine-checked Lean theorem whose premises are finite certificates. Those certificates are
not built yet; the solver evidence for them is partial and labelled as such.

1. **The route, as one Lean theorem.** `Dim8Lift.upper_of_certs` (`lean/Final.lean`; core Lean
   4.35 plus the repository's `LocalWindowModel`; axioms `propext`, `Classical.choice`,
   `Quot.sound`; no `sorry`, no `native_decide`). For 113 <= L <= 116 its premises are:
   - two cover tables that pass a Bool check: `t5` (54,604 entries) and `t6` (187,002 entries);
   - `Unsat` of the Q5 cover CNF and of the 35 Q6 cover CNFs;
   - `Unsat (cubeCnfC4 13 L r.mask r.size)` for each of the 2,161 representatives in `reps`.

   Its conclusion is that every snake of Q9 has at most 2L - 3 edges. **L = 116 gives 229**,
   independently of the K7 window machinery.
2. **The pieces.** They are in sections 1 and 4.
   - The reduction `snake_le_of_noPit`: no 13-path induced linear forest of Q8 on L vertices
     implies m <= 2L - 3. It needs no cap: a prefix with 2L - 2 edges is cut.
   - The cube bridge `no_pit_of_unsat`.
   - The glue `noPit_of_cubes`: a largest 6-subcube is moved to copy 0 by stored generator
     words, and the forest is transported along Aut(Q8).
   - The orbit cover `coverOK_of`: two levels (Q5 halves, then Q6 copies), each a cover CNF with
     a Lean bridge plus a table of generator words.
3. **Where the route bottoms out.** The best known forests have g8(13) = 112. Even if that is
   exact the route gives 223 at best (221-223), never ~220.
4. **Q7 validation (solver evidence).** g7(8) = 56: all 2,161 cubes are UNSAT, 1,655 s in all.
   This was open after milestone 29.
5. **Q8, level 116, i.e. L = 116 (worth 229).**
   - The full run is in progress: `data/q8_L116_c4_results.jsonl` is pushed every ~30 min. It
     uses the Lean-exported CNF `cubeCnfC4`. Every cube finished so far is UNSAT; none is SAT.
   - Size-29 cubes take a median of ~107 s and up to ~1,000 s (4 jobs on 4 cores).
   - The 24 cubes whose fixed copy has 31 or 32 vertices are much harder. One of size 31 took
     2,179 s. Those of size 32 are unknown after 30 min, even with 300 lex-leader clauses. They
     need adaptive splitting (`scripts/split.py`).
6. **Cost.**
   - Solving takes ~190 core-hours for level 116.
   - LRAT: measured 77 k trimmed hints per solver-second (25 s solve: 1.88 M hints; 104 s:
     8.0 M), so ~50 G hints and ~3,000-3,500 Lean CPU-hours.
   - Lower levels: the same cubes are 2-3.4 times harder at L = 115 (227) and 4.5-6.6 times
     harder at L = 114 (225).
   - The table checks need ~1.5 CPU-hours of kernel time. Each cover CNF solves in under 30 s.

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

## 4. The Lean chain and what is left to certify

All modules are in `lean/` and are built with `bash lean/build.sh` (core Lean 4.35; it takes
`LocalWindowModel` and `LratV3` from `work/final_lean`).

| module | content | key theorem |
|---|---|---|
| `Sums`, `Bits`, `Lift1`-`Lift5`, `Dim8Lift` | the facet-split reduction | `snake_le_of_noPit` |
| `Counter` | sequential counter (Sinz) and its soundness | `atMost_sound` |
| `CubeCnf` | the cube CNF as a Lean definition (`cubeCnfC4 c L A k`, 857 k clauses); `Export.lean` writes it as DIMACS | |
| `CubeBridge1`-`5` | a `Pit` with copy 0 = A and all other 6-subcubes <= k satisfies it | `no_pit_of_unsat` |
| `Sym`, `SymPit` | 36 generators of Aut(Q8) (28 coordinate transpositions, 8 flips; bit facts by `decide`); a `Pit` is transported along each | `pit_gen` |
| `Glue1`, `Moves`, `Glue2` | subcube counts and their transport; a largest 6-subcube is moved to copy 0 by 112 stored words (checked by `decide`) | `noPit_of_cubes` |
| `CoverCnf`, `CoverBridge` | generic cover CNF on Q5/Q6 (degree, selection-conditioned levels, counters, blocking clauses) | `cover_of_unsat` |
| `TabDefs`, `CoverDefs`, `Cover2` | the two-level orbit cover | `coverOK_of` |
| `Final` | everything together | `upper_of_certs` |

The orbit cover works as follows.

- The copy-0 forest has >= 29 vertices. Flip coordinate 5 if needed, so that the low half is the
  larger one; it then has >= 15 vertices.
- By `c5Cnf` (UNSAT) the low half is one of the 54,604 raw Q5 forests. A stored word in B5 maps
  it to one of the 35 representatives r5.
- By `c6Cnf r5` (UNSAT) the copy is one of the listed extensions of r5. A stored word in B6 maps
  it to one of the 2,161 representatives, whose size equals the copy size k.
- The tables are checked by a Bool function (`chk`), so they are not trusted:
  - each word consists of B_n generators;
  - each entry maps its raw set exactly onto its representative;
  - each representative is in `reps`.

Still to produce (all finite):

1. **Table checks.**
   - `scripts/gentables.py` and `scripts/genlean_tables.py` write 122 data modules of 2,000
     entries each into `lean/gen/`. They are not committed: 17 MB, regenerable from the
     enumerators.
   - Each chunk is checked by `decide +kernel`; a t6 chunk took 48 s.
   - Then `t5.all chk = true` and `t6.all (...) = true` follow by concatenation.
2. **36 cover certificates.** The cover CNFs are small (99 k-181 k clauses) and each solves in
   under 30 s (`scripts/cover.py`, `data/cover_check.json`; same CNFs as the Lean definitions up
   to counter numbering).
3. **2,161 cube certificates at L = 116, `Unsat (cubeCnfC4 13 116 A |A|)`.**
   - Measured on a 25 s cube: the LRAT core has 75.5 k of the 858 k input clauses and uses 54 k
     distinct variables (maximum variable 1.03 M). The trimmed proof has 1.88 M hints.
   - The repository's replay (`gen_lean_lrat.py`, LratFast2F up to 17-bit words) replays a
     core. To use it, three pieces are needed:
     - variable compaction plus a renaming lemma (injective renaming preserves
       unsatisfiability);
     - a check that each core clause is the clause of the stated index in `cubeCnfC4`: one
       ordered walk over the generated list;
     - the per-certificate `Unsat (core)`.
   - No new checker kind is needed, but this integration is new glue.
   - Cubes over ~780 s exceed the 60 M-hint cap and are split into literal-cube leaves
     (`split.py`), each a separate certificate with a literal case-split cover.

| item | count | size | Lean cost (at 0.23 ms per hint) |
|---|---|---|---|
| table chunks | 122 | 2,000 entries each | ~1.5 CPU-h of kernel time |
| cover certificates | 36 | < 30 s solves, a few M hints each | < 100 CPU-h |
| cube certificates, size-29/30 | 2,137 | ~77 k hints per solver-second, ~35 G in all | ~2,200 CPU-h |
| size-31/32 cubes | 24 | unmeasured tail, split into leaves, ~10-20 G | ~1,000 CPU-h |

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

## Worker command (level 116 = bound 229, for farm machines)

On a machine with Lean 4.35 at `/opt/lean-4.35.0-linux` and CaDiCaL 2.1.3 on PATH, in a checkout
of this branch:

```bash
cd milestones/39-dim8-lift && bash lean/build.sh >/dev/null    # builds lean/build/CubeCnf.olean (~3 min)
cd scripts
SKIP=../data/q8_L116_c4_results.jsonl SHARD=$S/$N GEN=lean ORDER=small \
  nohup python3 cubes.py 8 13 116 6 ../data/q6_29.txt ~/q8L116 20000 4 > ~/q8L116.log 2>&1 &
```

- S = 0..N-1 is the worker's share.
- `SKIP` drops the cubes already UNSAT in the committed results.
- `GEN=lean` solves the Lean-exported `cubeCnfC4`, i.e. exactly the CNF that the certificates
  refer to.
- Results go to `~/q8L116/results.jsonl`; the run is resumable.
- Memory is about 0.5 GB per job.
- The 24 size-31/32 cubes should go to `split.py` instead (60-300 s leaves).
