# Beyond 232: findings of 19-20 October 2026 and how they connect to earlier work

Status: working notes. Every bound below 245 in this milestone is **conditional**: the Lean theorems prove "no listed window occurs => at most N edges"; the windows are refuted by drat-trim-checked DRAT proofs of local CNFs, and the geometric step from a snake window to that CNF is not formalized. The unconditional, Lean-checked interval is still 191 <= a(9) <= 245 (`FinalAudit` of every reproduction manifest).

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
- **Normalisation:** map the snake by a cube automorphism `v -> sigma(v xor x_j)`, so the window has a canonical shape. Translation lemmas already exist; coordinate permutation does not.
- **G1, the geometric step:** store the CNF clauses the proof uses as data, tagged by kind. Prove once that a kernel-decided checker `validCore` makes them true under the assignment read off the normalised snake (ball membership, endpoints, counter wires).
- **G2, the refutation:** LRAT steps checked one theorem per step with clauses as bitmasks. The measured cost is about 28 ms per step plus 0.6 ms per hint, about 4x faster than the `work/lean112` checker.

**Estimated cost:**

| Bound made unconditional | Certificates | LRAT steps | Kernel time |
| --- | --- | --- | --- |
| 244 (`upper_244_of_no_two_two_three`) | 2 | 18,700 | about 20 min |
| 242 / 241 | 22 | about 375,000 | about 7 h |
| 239 | 145 | about 4 million | about 3 days |
| 235 / 233 / 232 | 2,635 / 8,182 / 15,959 | 10^7.7 - 10^8.8 | months to years |

**Cheapest first milestone:** 244 unconditional, which moves the proved interval from 245 to 244 with two certificates. Before the large chains, the proofs must shrink by about 100x. Options: minimisation weighted by proof cost (oracle time predicts certification time, log correlation 0.95), incremental certification per shape, and re-solving on the used clauses.

## 5. Lower-bound side

- See README "Lower bound" and `milestones/08-exhaustive-search`.
- No snake longer than the published 191 edges (Orland et al., arXiv:2607.15270) was found.
- A longer construction would be an unconditional improvement, but its chance of success is low.
