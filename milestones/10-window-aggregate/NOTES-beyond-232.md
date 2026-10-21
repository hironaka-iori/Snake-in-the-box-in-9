# Beyond 232: findings of 19-20 October 2026 and how they connect to earlier work

Status: working notes. Every bound below 245 in this milestone is **conditional**: the Lean theorems prove "no listed window occurs => at most N edges"; the windows are refuted by drat-trim-checked DRAT proofs of local CNFs, and the geometric step from a snake window to that CNF is not formalized. Since 21 October the unconditional, Lean-checked interval is **191 <= a(9) <= 239** (`verified_interval_191_239`; 244 first, then 242 and 241, then the 145 direction-aware windows of 239 with the same bridge, `milestones/07-window-223/bridge/README.md`).

## 1. The six-centre ceiling is 9/2

- The cap-7, six-centre automaton (L = 7) reached mean 9/2, which gives the conditional bound 232 with start-state accounting (`README.md`, "Start-state accounting").
- Its last minimum cycles first survived only because their windows had timed out at the 10 s query limit. Retrying them in the radius-four ball (`refine_fast.py --long-timeout`) refutes most of them: the larger ball is faster on these windows, 28-38 s against 205 s at radius three.
- After that, one cycle remains locally feasible. Its counts are 4, 8+, 4, 3, 5, 3 along directions `0,1,2,0,3,4,2,...`, and every window of two to six centres on it is feasible at radius three, four **and five**. So 9/2 is a hard ceiling for windows of at most six centres at these radii.
- This continues the pattern recorded in "Ceilings of count-only window methods" (README) and in milestone 09 (`milestones/09-research-directions`, limits of uniform singleton-density bounds): each family of local premises has an explicit periodic adversary, and the next lever is a larger window.

## 2. Seven-centre windows

- Seven-centre windows on the same periodic pattern are refuted in about one second at radius three or four.
- The automaton with eight directions of memory, windows of up to seven centres and cap 7 has 132 shapes, 34.6 million states and 194.6 million allowed edges. Engineering that made it run on this 15 GB machine:
  - `lean_automaton.py`: CSR edge arrays at about 22 B per edge instead of 68, and Howard in place;
  - `fastround.py`: incremental edge removal, and near-minimal cycles from the reduced-cost subgraph;
  - `lean_minimize.py`: the minimiser, about 2.5 GB instead of 23-25 GB.
- Progress of the refinement (`data/refine_L8_k7_K7_r3.log`):
  - it starts at 68/15 because every cached exclusion of at most six centres still applies;
  - it reached 107/23, about 4.652, by 20 October 06:00 UTC.
- 231 needs a mean above about 4.679. With eight directions of memory the constant is `8 P - Q + D`, and the bound is `floor((9170 Q + 8 P + D) / (P + 35 Q))`.
- The cap-5 variant (6.2 million states) reached only 4.24 after 45 rounds, because lumping counts at six hides the structure.

**Status at 20 October, 10:50 UTC.**
- The seven-centre cap-7 refinement reached mean 103/22, about 4.682, on the solver-refuted windows (these are not certified yet).
- On those windows the exact walk bound of the automaton (`vertex_bound`, computed by `lean_minimize.py --lam 103/22 --start`, 564 million edges, 4.9 GB, 5 minutes) is already **231**.
- The start-accounting potential still gives 232: at 103/22 it needs `D < -28`, and the best start potential has range 884.
- As the mean rises, the requirement relaxes: at 89/19 it is `D < -14`, at 75/16 it is `D < 0`.
- Those denominators exceed the 8-bit SWAR fields, so the Lean side needs 16-bit fields (in progress).
- The set for 103/22 keeps 57,831 windows (8,535 of them seven-centre). Most are not certified yet.

**Status at 20 October, 15:10 UTC: 231 is proved only provisionally.**
- The refinement reached mean 89/19 (about 4.684). At that mean the start potential has `D = -15`, and `-14` is enough: `lean_minimize --lam 89/19 --start` keeps 58,817 windows (`data/minimal_L8_k7_K7_r3_89_19.json`) with potential bound and exact walk bound both **231**.
- The generator with 16-bit fields builds a chain from that set and proves `upper_231_of_direction_windowsK7R34C7W16` with standard axioms (184 modules, about 30 minutes, scratch only). Its premise list comes from solver answers, not certificates, so it is not in the repository yet.
- Certification of the 44,738 uncertified windows of the set is running (`data/certify_direction_231.log`, 938 done before a machine restart). At the present rate it needs days; an incremental per-shape certifier is being built to cut that.

**Status at 21 October, 11:00 UTC: conditional 231 proved by another route.**
- Every six-centre window has empty-square share sum at least 21 (34 count-free shape certificates, DRAT-checked). Adding that to the 232 chain gives `upper_231_of_direction_windows_and_shares` (README, "Empty-square shares: conditional bound 231").
- For 230, the 132 seven-centre shapes are certified at share sum at least 27 (`data/share/final_b_X26.jsonl`). With the 89/19 set this gives 230.97, so 230, once all 58,817 windows of that set are certified and the 16-bit chain is wrapped the same way.

**Status at 21 October, 17:00 UTC: conditional 230 proved.** All 58,817 windows of the 89/19 set are certified. The seven-centre chain proves 231, and with the 132 share-shape certificates it proves 230 (README, "Seven-centre windows and shares").

## 3. Lean side for seven-centre chains (prototype, not yet in the repository)

- A generator prototype (scratchpad `genk7/`) produces and compiles a provisional L = 8, k = 7, cap-7 chain end to end, with standard axioms only.
- Measurements:
  - 46 MB of source split into Base, 11 potential modules and Data;
  - 132 shards of about 4 s each;
  - the Table module takes 247 s;
  - every module stays under 3.2 GB.
- The start table clips each field at 127, which is sound because it is a stronger statement.
- The binding limit is now the 8-bit transition fields, `P + R <= 128` and `8 Q + R < 128`.

## 4. Making bounds unconditional: plan and precedents in this repository

**Earlier work in this repository that this builds on:**
- `milestones/06-radius-five`: a 567-clause Boolean core checked in Lean (`work/final_lean/BallCertificate.lean`, `BallClauseLogic.lean`). Its geometric interpretation and normalization are unfinished.
- `milestones/07-window-223`: the (2,2,3) radius-three window certificates behind `upper_244_of_no_two_two_three`, `upper_242/241_of_certified_windows`.
- `work/lean112`: a complete geometric bridge plus kernel-checked unit propagation (`LocalRup.lean`, `TreeRup.lean`) for fixed prefix regions of the bank snakes. Measured cost there: about 0.2 s per RUP step, and about 0.7 s per geometric clause proved by a tactic.

**Plan** (from a design study on 20 October):
- **Normalisation:** map the snake by a cube automorphism `v -> sigma(v xor x_j)`, so the window has a canonical shape. Translation lemmas already exist, and coordinate permutation is now proved in `work/spectral/stronger/CubePermutation.lean`, which is part of the reproduction with standard axioms. That file shows `permV σ` is a bijection preserving adjacency and distance; that `cubeMap σ x p` is a snake of the same length with `pathDir` mapped by σ; that `localAlpha`, `countSeq` and the (2,2,3) window are invariant; and that any window with pairwise distinct directions can be normalised (`exists_normalizing_cubeMap`). Still open for 244: the two window shapes, the clause-by-clause check G1, the kernel LRAT check G2 (3,744 + 24,895 steps), and the assembly.
- **G1, the geometric step:** store the CNF clauses the proof uses as data, tagged by kind. Prove once that a kernel-decided checker `validCore` makes them true under the assignment read off the normalised snake (ball membership, endpoints, counter wires).
- **G2, the refutation:** LRAT steps checked one theorem per step with clauses as bitmasks. The measured cost is about 28 ms per step plus 0.6 ms per hint, about 4x faster than the `work/lean112` checker.

**Estimated cost:**

| Bound made unconditional | Certificates | LRAT steps | Kernel time |
| --- | --- | --- | --- |
| 244 (`upper_244_of_no_two_two_three`) | 2 | 18,700 | about 20 min |
| 242 / 241 | 22 | about 375,000 | about 7 h |
| 239 | 145 | about 4 million | about 3 days |
| 235 / 233 / 232 | 2,635 / 8,182 / 15,959 | 10^7.7 - 10^8.8 | months to years |

**Done:** 244 is unconditional, moving the proved interval from 245 to 244 with two certificates (`milestones/07-window-223/bridge/README.md`). The total kernel work is about 260 s, far below the estimate, because the trimmed LRAT proofs have 1,629 and 17,101 steps. Before the large chains, the proofs must shrink by about 100x. Options: minimisation weighted by proof cost (oracle time predicts certification time, log correlation 0.95), incremental certification per shape, and re-solving on the used clauses.

## 4b. Count-free local certificates do not reach 225 (21 October, solver evidence)

The question was whether a few count-free window certificates could replace the count automaton for an unconditional bound. Take ω(x) = 21 α(x) + share(x). Then `Σ ω <= 21 (9214 - 35 v)`; the identity `T + 2 s0 = 9214 - 35 v` is an equality, because `T = 21 v + 14 - 2 D2` and `s0 = 4600 - 28 v + D2`, where D2 counts non-consecutive path pairs at distance 2. There are m - k windows of k centres, each centre lies in at most k of them, and each endpoint has ω >= 84. So 224 needs every k-centre window to have Σ ω >= about 124 k (k = 6: 746).

Local minima are far lower:
- **ω, radius 3:** 0 at k = 1, 88 at k = 2, between 201 and 259 at k = 3, at most 353 at k = 4.
- **ω, radius 4:** 29 at k = 1, 96 at k = 2. Radius 3 leaves the degree of the corners' neighbours unchecked.
- **Share alone:** at least 21 at k = 4, at least 37 at k = 5, at least 21 at k = 6, at least 27 at k = 7.
- **Real snakes**, for comparison (the minima over the 131 bank snakes, the witness and the counterexample): ω 217, 361, 539, 706, 874 and 1077 for k = 2..7, and share 179 for k = 6. Even these give 225 only from k = 3 and 219 at k = 6.

So the count automaton stays necessary. A share bonus on the unconditional 239 chain (L = 6, windows of four centres, `10 m <= 3 Σ α + 60`) gives 237-238 with these certificates, and 231 even with the real-snake share minimum. The cost of an unconditional bound below 239 is therefore the kernel cost of thousands of window premises. That is the target of the checker work: FastRup (bridge/fast) gives 2.3-3.6x, and one shared incremental proof per direction shape is being measured.

## 4c. Kernel cost of window premises: measured levers (21 October)

The cost unit is LRAT hints, at about 70 µs each with FastRup (2.3-3.6x faster than WinRup).

| Lever | Hints saved | Notes |
| --- | --- | --- |
| Lex-leader symmetry breaking per window | 3.6-4x | free and parallel; the Lean symmetry lemma exists (D239Lex) |
| One incremental session per direction shape (CaDiCaL `--lidrup`, one cube per window, backward trim from all targets) | 1.8-3.2x, 2.07x overall | grows with windows per shape; the proof becomes one sequential chain per shape |
| One CNF per shape with totalizer counters | none for G2 | G1 checked once per shape instead of once per window: 52 checks instead of 15,959 |

Estimated totals with symmetry breaking and sharing: the 232 set about 5e9 hints (about 100 kernel CPU-hours), the 235 set about 4e8 (7-10 CPU-hours). The current certificates, with no symmetry breaking, would need about 4e10 and 3e9.

The failed assumption cores use only 4-6 of the 10-12 count-range literals of a window. So the premises are far more specific than the refutations need, and generalising them to count boxes is the next lever being measured.

## 5. Lower-bound side

- See README "Lower bound" and `milestones/08-exhaustive-search`.
- No snake longer than the published 191 edges (Orland et al., arXiv:2607.15270) was found.
- A longer construction would be an unconditional improvement, but its chance of success is low.

## 6. Previous research on upper bounds (literature check, 20 October 2026)

A web check of the literature was made. Only search-result snippets were reachable: arXiv, OEIS, Wikipedia and the publishers' pages were blocked by the network proxy. On that evidence, nothing better than the counting bounds near 2^(n-1) has been published for Q9, and no SAT, DRAT or proof-assistant upper bound has been published for snakes or coils.

**Analytic upper bounds.** All are counting or weighting arguments, and most are stated for coils (induced cycles), so carrying them over to open snakes needs a separate argument.

| Source | Bound at n = 9 |
| --- | --- |
| Trivial / Huang (2019) | 255 edges (the repository's earlier Lean bound) |
| Snevily (1994), `2^(n-1) (1 - 1/(20n - 41))` | about 254, if the formula applies at n = 9 (its stated range is unverified) |
| Zémor (1997) | asymptotic only |
| Emelyanov-Lukito (2000) | best only for 37 <= n <= 19079 |
| Lukito-van Zanten (2001), square-face counting | value at n = 9 not found |

The Lean-checked 245 of this repository (milestone 05) and the conditional bounds of this milestone are well below all of these.

**Exact values for n <= 8.** These come from exhaustive search with symmetry or isomorph rejection, without proof certificates:
- Kochut (1996), Q7 coils;
- Östergård and Pettersson (2015), snakes up to Q8, 98 edges;
- Hood, Recoskie, Sawada and Wong (2015), spread-k snakes and coils.

**Lower bounds for Q9 come from construction:** Wynn (2012), 190 edges; Kinny (2012); Meyerson et al. (2015); Allison and Paulusma (2016); Orland et al. (arXiv:2607.15270), 191 edges.

**Citations verified from bibliographic snippets:**
- K. Deimer, Combinatorica 5 (1985) 109-120.
- F. I. Solov'eva, Metody Diskret. Analiz. 45 (1987) 71-76.
- H. L. Abbott and M. Katchalski, J. Combin. Theory Ser. B (1988), volume 44 or 45 (the snippets disagree).
- H. S. Snevily, Discrete Math. 133 (1994) 307-314.
- G. Zémor, Combinatorica 17 (1997) 287-298.
- P. G. Emelyanov and A. Lukito, Discrete Math. 218 (2000) 51-59.
- P. R. J. Östergård and V. H. Pettersson, Graphs Combin. 31 (2015) 1019-1028.
- E. Wynn, arXiv:1201.1647.
- D. Allison and D. Paulusma, arXiv:1603.05119.
- A. Palombo et al., SoCS 2015.

The paper draft (`paper/snake9_research.tex`) does not yet cite Kautz (1958), Danzer-Klee, Douglas, Deimer, Solov'eva, Abbott-Katchalski, Snevily, Zémor, Emelyanov-Lukito or the search papers, and does not compare with Snevily's or Zémor's bounds.
