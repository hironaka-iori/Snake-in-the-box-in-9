# Overlapping empty-square windows and selective history

Research date: 22 October 2026. This milestone tests whether the separate local witnesses behind the collaborator's period-three share obstruction can agree on overlapping vertices. It does not establish a new global bound or determine the optimum in Q9.

## Geometric result

The four tested eight-transition patterns are:

| Case | Directions after coordinate renaming | Internal singleton counts |
|---|---|---|
| 0 | 0,1,2,3,0,1,4,3 | seven counts all equal to 4 |
| 1 | 0,1,2,3,0,4,2,3 | seven counts all equal to 4 |
| 2 | 0,1,2,3,4,1,2,0 | seven counts all equal to 4 |
| 3 | 0,1,2,3,4,1,2,5 | seven counts all equal to 4 |

Every one is excluded by the ordinary radius-four window constraints, without a share cap and without added cycle cuts. Each finite refutation and its interpretation for arbitrary snakes passed Lean. The combined classification, selective-history lemmas, and all fifteen axiom audits also passed. **The completed gate is recorded in `data/verification.json`, with the individual axiom audits in `logs/`.**

The relevant five-centre direction types are A = 012304 and B = 012301, considered up to coordinate renaming and reversal. The collaborator's all-counts-four period-three cycle uses two A windows and one B window. Joining them produces the four patterns above. Python enumerates all 132 normalized induced eight-transition shapes. Independently, `JoinClassification.lean` checks the four-way classification for the three possible normalized first-six prefixes and all two-coordinate suffixes in Fin 8. `JointObstruction.lean` combines that finite classification with the four geometric exclusions. The coordinate-normalization hypothesis remains explicit in the combined theorem.

This result removes the particular period-three obstruction once seven-centre consistency is retained. It does not contradict the collaborator's ceiling for its original five-centre table, since that table allows independently chosen local configurations.

## Compact state refinement

The existing graph already remembers seven transition directions. The extra information needed is the length of the most recent run of singleton count four, capped at six. For a new count a, update this value r by

```text
if a = 4: r := min(6, r+1)
otherwise: r := 0
```

The exclusion triggers precisely when the old value is six, the new count is four, and the eight directions have one of the listed shapes. Four Lean lemmas verify the update, its correspondence with an actual suffix of fours, the seven-entry trigger, and the state-count arithmetic.

All states whose last four counts are not `(4,4,4,4)` already determine this run length. Only that one count tuple needs three versions, representing runs of length four, five, and at least six. With 34 direction states, the total increases from 34·6^4 = 44,064 to 34·(6^4+2) = **44,132**, adding **68** states.

The diagnostic graph incorporates the radius-four oracle and share-loop records pinned to `8ad204ffa32bb3bb114891ab089a50b83d0fc10e`. It has 212,394 pruned edges before the four exclusions and 212,390 afterward. Saved cycles have these exactly checked means:

| Table | Before | After |
|---|---|---|
| Recorded share lower bounds | 119/29 | 119/29 |
| Recorded local-witness values | 1699/360 | 859/180 |

The second row changes the cycle found from the all-four pattern to a count pattern `(3,3,6+)`. Its share entries are 95, 88, 95. The first row is unchanged. Thus the present lower estimate has not improved. The exact cycle means are verified; the script does not supply a complete minimum-mean potential certificate, a proof of the solver-derived share table, or endpoint accounting. No global upper bound follows from this diagnostic alone.

An earlier diagnostic omitted additional radius-four oracle exclusions and had lower mean 42/11. It is retained as `data/selective-graph-initial.json` with its script. The later result includes those exclusions and recovers the collaborator's reported lower mean 119/29. These two runs must not be conflated.

## Certificate evidence

The four cores have respectively 3,282, 2,982, 4,174, and 2,508 clauses, with 1,601, 1,612, 1,708, and 1,472 active variables. They use 3,095,844 LRAT hints in total. Each full native CaDiCaL proof was independently checked by drat-trim; the extracted core was then re-solved for LRAT and translated into Lean replay modules. Clause provenance is checked against a regenerated tagged geometric model. The final Lean statement does not trust either solver or the Python proof generator.

The fifteen completed axiom audits cover four finite refutations, four geometric interpretations, two classification results, the combined obstruction, and four selective-history lemmas. They contain only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound` as applicable. An audit file containing `sorryAx`, a reduction axiom, or an error is a failure.

Two shorter six-centre patterns, 0123014 and 0123042, were initially UNKNOWN at 50,000 conflicts. Longer tests excluded both without added cycle cuts, in approximately 6.8 and 5.3 seconds. Those shorter exclusions remain solver-only and are not used in the checked seven-centre argument. No claim that seven centres is minimal is made.

A comparison against the collaborator's 38,699-case certificate index at `f83d139d01977b3d7ea4d3706af7b94a173ae42d` found none of these exact seven-count tuples. That is a limited repository comparison, not a claim of novelty in the literature or exclusion of every possible implication of prior work.

## Reproduction

Use the Lean 4.19.0 and pinned mathlib environment described in milestone 28. `scripts/build.ps1` creates a fresh build folder and reuses milestone 28's compiled support and its recorded geometry dependencies; it is an incremental build, not a fresh rebuild of the whole proof closure. The scripts contain the Windows paths that must be adjusted elsewhere.

```text
python -X utf8 scripts/archive.py --unpack
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/build.ps1
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check_join.ps1
python -X utf8 scripts/verify.py
```

The generator `scripts/certify.py` regenerates the four certificates, including independent DRAT verification, using the runtime dependencies from milestone 28. The compressed archives and their raw contents are hashed in `data/archives.json`. Proof generation and replay are separate steps. The verifier requires the same Python dependency paths because it rebuilds the tagged CNFs.

`scripts/selective_graph.py` retrieves the pinned upstream oracle records and repeats the graph experiment. It checks every edge of the reported cycles and their means exactly. This script does not run new SAT searches. `scripts/joint.py --mode plain` repeats the four ordinary feasibility tests. Its additional `individual` and `total` modes can impose joint share caps, but those modes were unnecessary after the ordinary exclusions were found and were not used as evidence here.

## Next step

The final 22 October refresh found `research/unconditional-241` at `d4936d72`, with a 235 replay plan; `claude/relaxed-keller-60ks7i` at `86bd4daf`, with conditional 230 work and a faster RUP checker; and Tommy Ma's `research/unconditional-231-230` at `e931afe8`. The latter explicitly records unfinished count coverage and states that unconditional 231/230 remain incomplete. Reviewed source hashes and full commits are in `data/github-refresh.json`. These newer proof chains have not been imported or independently rebuilt in this milestone; its experimental oracle remains pinned to 8ad204ff.

The first tests of the surviving `(3,3,6+)` cycle are saved in `data/next-*.json`. All four joined patterns are solver-UNSAT when every 6+ entry is exactly six. Allowing the full range 6 through 21 leaves cases 0 and 1 UNSAT, while cases 2 and 3 have independently checked acyclic local witnesses with count tuples `(11,3,3,9,3,3,11)` and `(9,3,3,10,3,3,9)`. Their positive existence does not prove those larger counts are individually minimal, and no extension to a complete snake is claimed. All 99 saved cycle cuts from these two searches passed independent checks. The six new UNSAT results still need proof certificates.

Certify the two interval exclusions and the exact-six exclusions. The latter would justify charging at least one unit of singleton-count excess on a surviving coarse window, since at least one 6+ entry must exceed six. This offers a way to correct the numerical loss from coarse symbols without expanding every symbol in the entire graph. A global result still requires verified numerical premises, an all-sequence potential or packing argument, and endpoint corrections.
