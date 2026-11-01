# Count-free empty-square charging

Research checkpoint begun 1 November 2026, continued 2 November. This directory uses the ten-case graph and the checked share-120 theorem from commit `48919e3d`. The project's unconditional interval remains **191 <= a(9) <= 235**, with length measured in edges. The investigation below has not established a new global bound.

## Target and notation

For a snake vertex x, define its integer share by

\[
\sigma_{12}(x)=\sum_{q\sim x}
\left\lfloor\frac{12e_0(q)}{d_S(q)}\right\rfloor,
\]

where e_0(q) counts empty squares incident with q and d_S(q) is the number of selected neighbours of q. The denominator is positive for every summand at a selected x. A six-transition window has five internal centres. Its direction word is considered up to coordinate relabelling and reversal. Digits in a word identify coordinates; repeated digits identify the same coordinate.

The new direction is to prove lower bounds for the sum of these five shares **without singleton-count hypotheses**. This replaces many count-specific statements with a small direction-shape catalogue. The bounds 0 <= alpha_i <= 21 used by the encoder are automatic for internal centres.

## Verified graph calculations

The refreshed source graph has 1,601,856 states and 4,947,008 edges. The share-120 theorem raises 1,280 weights. Its exact minimum mean remains 480. The complete tight cyclic subgraph contains 17,506 edges, 5,791 states and five components, representing 477 canonical count windows. All its recorded share lower bounds are zero.

Exhaustive topological deletion over all 64 subsets of its six direction shapes finds exactly four minimal shape covers of all tight cycles:

- {012345, 012032, 012034}
- {012345, 012032, 012310}
- {012345, 012314, 012034}
- {012345, 012314, 012310}

A positive additional charge on every occurrence of one such cover eliminates every cycle attaining the old mean. This does not identify the new mean by itself. The calculation is in `data/shape-cover.json`; `scripts/check_shape_cover.py` reproduces it without numerical tolerances.

Assuming share >=12 for shapes 012345, 012032 and 012034 gives exact mean **485**, potential range **603**, and

\[
m\le\frac{1103443}{4685},\qquad m\le235.
\]

Every modified weight, every one of the 4,947,008 potential inequalities, and an attaining eight-edge cycle were independently reconstructed. See `data/countfree-012345-012032-012034-verification.json`. Weights use the maximum of bounds on the same five centres; they are never added together.

For the existing fixed potential targeting 234, the distinct-direction share-12 rule reduces additional count obligations from 14,142 to **14,060**. All three rules reduce them to **14,001**. These are exact least-cover calculations for the fixed graph, candidate basis and potential, supported by mandatory singleton clauses. They remain conditional on the outstanding count premises and global interpretation.

## Sharper conditional target

An exhaustive enumeration gives twelve oriented six-transition shapes, or nine up to reversal. If all nine have five-centre share >=16, the graph has exact mean **496**, range **600**, and an attaining three-edge cycle. Independent reconstruction verifies every edge inequality. The resulting conditional arithmetic is

\[
W\ge496(m-8)-600,\qquad W+4200m\le1098960,
\]
\[
4696m\le1103528,
\qquad
m\le\frac{137941}{587}<235,
\qquad m\le234.
\]

The strict margin at m=235 is **32**. `lean/CountFreeTarget.lean` checks this implication in Lean; the printed axioms are propext and Quot.sound. The two displayed bounds on W are hypotheses of that theorem. The universal share-16 statement and the complete snake-to-graph and global-share assembly remain unresolved. This is a sufficient target, without a claim that it is necessary or optimal.

The preferred certificate set now allows unequal bounds:

| Direction shape | Required five-centre share |
|---|---:|
| 012031 | 16 |
| 012032 | 16 |
| 012034 | 20 |
| 012301 | 16 |
| 012304 | 16 |
| 012310 | 12 |
| 012314 | 16 |
| 012340 | 16 |
| 012345 | 16 |

All nine required Boolean refutations have passed independent DRAT checking and exact encoder reconstruction. The 012301 certificate includes sixteen valid eight-cycle exclusions. The other eight use no additional cycle cuts. `data/portfolio.json` identifies one certificate per premise. Coordinate relabelling and reversal must be justified when converting these representatives into arbitrary-snake inequalities.

The uniform share-16 criterion now also has independently checked Boolean certificates for all nine shapes. The difficult 012310 case was solved with a different backend; its independent checker needed 160.8 seconds after an initial timeout. The mixed portfolio contains 384,808,718 raw proof bytes, compared with 511,148,563 for the smallest saved uniform portfolio. This comparison measures stored proof size only; it does not establish a Lean replay speed advantage.

This unequal assignment also has exact mean **496**, range **600**, and the same bound **137941/587 < 235**. Every modified weight and every potential inequality passed independent reconstruction, with an attaining three-edge cycle. It avoids the difficult uniform share-16 requirement for 012310. Reducing only that shape to 12 without increasing 012034 to 20 gives mean **1484/3**, range **1788** in denominator-three units, and bound **827635/3521 > 235**. These comparisons retain the correct potential scaling.

The nine share statements provide an alternative to the additional 14,142 count premises in the earlier fixed-potential plan. Existing checked count rules remain part of the source graph. The nine local share proofs and global assembly are still required; completed native certificates do not establish an unconditional bound of 234.

## Controls and failed shortcuts

- A checked local acyclic configuration has zero share at a single centre. A positive pointwise bound does not follow from this local relaxation.
- The initial forced-unselected neighbours of a six-transition path contain no whole empty square, for each of the nine shapes. The direct forced-neighbour lower bound is therefore zero. Further snake constraints are necessary for this argument.
- For shape 012301, a cap-15 SAT configuration has 223 selected vertices, centre counts (1,1,1,1,1), and zero total share. It contains sixteen eight-cycles. It is not a snake or an acyclic local witness. Excluding those cycles gives a separate UNSAT solver result; certificate status is recorded separately.
- All 24,366 windows in 131 independently checked complete 191-edge bank snakes have total share at least 142. The minima are examples and do not prove a universal bound. The bank hash and attaining windows are retained in `data/bank-share.json`.
- The stronger distinct-direction cap-23 native attempt timed out. Short cap-23/47/71 searches also returned UNKNOWN. These outcomes supply no exclusion.

## Proof status and continuation

The count-free distinct-direction share-12 theorem has passed Lean, including its arbitrary-snake wrapper: **221 modules and 86 printed theorem audits**. The five internal counts have no additional hypotheses. The proof checks 73 geometric semantic batches, the 9,303-clause core and its 3,478,301 LRAT hints. The final axioms are limited to propext, Classical.choice and Quot.sound; no sorry, admit or native_decide is used. See `share-proof/data/proof-audit.json`. A combined-import check confirms compatibility with the earlier share-120 theorem; its generic append lemma has a distinct name to avoid duplicate declarations. Four additional axiom audits cover these imports and the conditional arithmetic.

Several share-12 and share-16 native certificates are saved independently. `data/*-certificate.json` distinguishes verified DRAT, SAT relaxations, and timeouts. A DRAT result proves only its Boolean formula is contradictory. The clause interpretation, coordinate normalization, cycle-cut validity where used, and Lean replay are still required for an arbitrary-snake statement.

The reused share bridge states its result in `coreShare`. Its equality with the separate global `shareN` representation remains a dependency, as does the full arbitrary-snake automaton interpretation. Neither the new local theorem nor exact finite potentials discharge these connections automatically.

Next priority: check the nine certificates in `data/portfolio.json` in Lean and complete their geometric interpretation. Prefer the mixed portfolio's smaller stored proofs; retain the now-complete uniform certificate catalogue as an alternative. Preserve exact source graph hashes; historical six-case and eight-case edge indices are incompatible with this graph.

## Reproduction and source boundaries

`prepare.py`, `critical.py`, and `verify.py` reconstruct and verify the source critical family. `enumerate_shapes.py` and `check_shape_cover.py` reproduce the finite shape enumeration and cover calculation. `countfree_effect.py`, `analyze_countfree.py`, and `verify_countfree_model.py` generate and independently check conditional comparison graphs. Pass `--all --share=16` to the first script for the sharper target.

`setup_countfree.py`, `prepare_lean.py`, and `assemble_countfree.py` generate the isolated share-12 proof. `replay_share.py` checks its semantics; `export_share.py` generates the LRAT replay modules; `complete_share.py` compiles the remainder; `audit_share.py` validates source hashes, clause correspondence and printed axioms. Existing repository dependencies are reused. No fresh rebuild of all inherited proof dependencies is claimed.

For the next nine proofs, rebuild the encoder from each selected metadata file, including its exact cycle cuts. Rename only active variables first and retain the original-clause mapping. Choose the replay literal offset from the actual active-variable count and the packed word width from both literal and replay-slot ranges. The share-12 proof's offset 8192 must not be copied without checking those ranges. Give each case its own module namespace, reuse shared support definitions, and check combined imports to catch duplicate declarations. `audit_native.py` records the core variable counts and minimum literal offsets.

`archive_evidence.py` preserves verified native formulas, proofs and cores in compressed files, plus the exact generated Lean sources and compact replay inputs. `restore_evidence.py` verifies hashes and restores missing inputs while refusing to replace differing local files. Raw proof data and compiled objects remain in ignored build directories; the archives support repository-based reproduction.

GitHub branch `RamseyCheck` was inspected at `e26fd1b7`. Its delivered count certificates and history exclusions are separate evidence; that branch explicitly reports no new global bound and no fresh Lean replay for its three count certificates. It was not merged into this experiment.

The paper and editor mirror remain identical at revision 66, with all three authors and the existing hyperlink settings preserved. Round 72 remains in progress; this checkpoint does not complete the exact Q9 problem.
