# Milestone 51: empty-square shares on critical windows

Research round 5 of 10 after manuscript revision 46. The selected direction is route 1, empty-square charging. The endpoint-demand route is outside this round.

## Checked local result

Let a snake contain six consecutive directions `(a,b,c,d,b,e)`, with the five named coordinates distinct. Suppose its five interior singleton-square counts are `(3,3,3,A,5)`, where `6 <= A <= 21`. Then the sum of the five integer shares at resolution 12 is at least **48**.

For a selected vertex x, the share is the sum over its nine neighbours q of `floor(12 e0(q)/dS(q))`. Here e0(q) counts empty square faces incident to q, and dS(q) counts its selected neighbours. Each denominator in this sum is positive because x is selected. This is the existing empty-square share definition.

The certificate uses empty-square and share clauses. Its ordinary local model is satisfiable: a matching saved radius-four forest has total share 263. Thus the new refutation does not merely rediscover an ordinary count exclusion. This local forest has not been extended to a full snake, and 48 is not claimed to be sharp.

All **26 Lean modules** built. **14 dependency audits** contain only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. The checks include the clause interpretation, the refutation, coordinate-frame invariance, the named-coordinate snake theorem, and common-window charge accounting. The final receipt is [data/verification.json](data/verification.json).

The native formula has 182,516 clauses and 22,809 variables. Its trimmed core has 6,681 clauses and 4,196 active variables; the semantic interpretation needs 6,525 variables. The Lean replay checks 353,479 hints. Four independent semantic assignments were checked against all clauses, and 142 positive local configurations were checked geometrically. The matching ordinary forest violates exactly the imposed share-cap clause.

## Exploratory range pressure

The previous count-only sweep completed five stages before the user's route selection. Its normalized minimum means were 27/7, 58/15, 147/38, 31/8, and 66/17. Those stages are retained as inputs, not continued as a separate research direction. Pass 6 is partial and has no completed graph; its ordinary witness supplies the positive control above.

The pass-5 critical family has 26 distinct five-centre windows. Independent share screening with cap 95 returned 17 INFEASIBLE, three FEASIBLE, and six UNKNOWN. The positive shares 95, 95, and 93 rule out a uniform lower bound of 96 over the entire family. Neither numerical INFEASIBLE nor UNKNOWN is represented as a Lean theorem.

Using the 17 proposed lower bounds gives the mixed transition weight

`336 b_new + 48 D + 42 c + Q`,

where b is the singleton count truncated at six, D is a joint excess demand, c is the prior share event, and Q is the largest applicable five-centre share bound within the seven-centre window. The maximum prevents adding overlapping local demands without justification. Combining two separately valid budgets gives a total at most 14 G, where `G = 24 T + sum sigma12`. The common-window multiplicity and mixed accounting are Lean checked; the full generated graph-to-snake argument remains pending.

An integer potential checked on all 3,184,668 retained edges and an attaining nine-edge cycle establish the conditional finite-model mean **35/9**. Its weighted mean is 3920/3 and potential loss 4480/3. The resulting conditional edge bound is 8277/35, which still rounds down to 236. The model relies on unreplayed numerical rules, including the proposed share bounds of 96. The single checked bound 48 does not validate that complete model.

## Contributor update and next target

At contributor commit `74ca83db9c218446211d4f24c5e5a07329fdd847`, the six-centre proof of **235** is complete. The final theorem and its successful standard-axiom audit were inspected and pinned in [data/contributor](data/contributor). The 635 new replay roots are recorded as complete. This entire dependency closure has not been independently rebuilt locally.

Accordingly, the contributor-checked interval is **191 <= a(9) <= 235**. The existing local paper remains at 236 pending its scheduled revision. This round's local share theorem does not improve either endpoint. The useful next target is 234: strengthen certified shares on surviving critical windows, use the completed 235 count argument as the baseline, and establish sufficient global charge including boundary losses. A local improvement alone does not supply occurrence frequency.

## Files and reproduction

- `lean/`: checked local share, geometric bridge, accounting, and generated certificate modules.
- `certificates/`: losslessly compressed native formulas and proofs; hashes in `data/archives.json`.
- `pass1` through `pass5`: completed exploratory count stages. `pass6`: partial stopped stage.
- `data/share-screen/`: all 26 share-screen outcomes and positive controls.
- `share-model/`: conditional mixed graph data and exact potential/cycle certificate.
- `scripts/verify.py`: source, core, archive, Lean-audit, and control consistency audit.
- `scripts/verify_geometry.py`: independent local-geometry and all-edge potential checks.
- `scripts/replay.py`: Lean dependency replay using the pinned local support builds; `--resume` retains source-hash-matching successful modules. A clean-machine dependency bootstrap is not supplied here.

The current paper and editor mirror were left unchanged, including authors and hyperlink settings. No PDF compilation is claimed for this round.
