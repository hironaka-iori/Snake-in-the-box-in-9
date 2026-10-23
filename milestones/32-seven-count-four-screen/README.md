# Consecutive singleton counts equal to four

Research date: 23 October 2026. The six-centre statement remains a hypothesis. Normalization, conditional density, and four individual geometric exclusions are checked; no new global bound is claimed.

The successive witness-table cycles in milestones 29 and 30 repeatedly use counts equal to four. After two further seven-centre shapes were solver-excluded, the investigation tested the direction-independent hypothesis that a snake cannot have seven consecutive internal singleton counts all equal to four. All 132 normalized induced eight-transition shapes returned UNSAT in the radius-four model. Testing one fewer centre then gave UNSAT for all **34** normalized induced seven-transition shapes.

The resulting stronger hypothesis is:

> No snake in Q9 has six consecutive internal vertices whose singleton-square counts all equal four.

Eighteen Lean audits now check the finite coverage, the reduction from arbitrary snakes to the 34 normalized cases, the implication from all 34 refutations to the conjecture, its conditional frequency consequence, and four individual refutations (cases 0, 1, 14, 22). The frequency consequence is that at least floor(N/6) of N consecutive internal counts differ from four.

All 34 native certificates have been generated and simulated; `data/native-inventory.json` records their sizes and replay status. Only the four completed cases are published as Lean proof sources and lossless certificate archives. The remaining generated proof sources are local intermediates excluded by this milestone's ignore rules. Their kernel replays remain open. `data/proof-verification.json` records the completed source hashes and checks; numerical generation does not certify the other 30 cases.

The new distance-three inequalities in [milestone 33](../33-distance-three-singletons/README.md) explain two of the small exclusions geometrically and provide stronger mixed-count restrictions. They achieve the same recorded witness-cycle improvement as the six-centre conjecture. They do not prove the conjecture for every direction pattern.

## Controls and limits

- A five-centre all-four local forest was found, checked independently by explicit vertex and square counting, and accepted as a fixed selection by an independent exact-square CP model. This prevents shortening the proposed local-model exclusion to five centres.
- Independent CP checks returned INFEASIBLE for six-centre cases 0 and 33, and UNKNOWN for case 23. Its unconstrained five-centre search initially returned UNKNOWN; the later fixed positive control returned FEASIBLE. All records are retained.
- All 131 saved 191-edge bank snakes were independently rechecked for distinct vertices and all-pairs adjacency, then scanned for count-four runs. Their maximum observed run is two. This is a bank observation, not a theorem for arbitrary snakes.
- Additional four- and five-centre screens are saved under `data/short-*`. The four-centre models all have local positive configurations. Several five-centre cases remain UNKNOWN. No unknown case is treated as an exclusion.
- A local forest can have many components ending at the boundary of the examined region. No extension of a local positive configuration to a complete snake has been established here.

## Files and reproduction

`scripts/screen.py` performs the initial seven-centre screen; `screen_six.py` performs the 34-case six-centre screen. Both save results incrementally. The local test uses the existing tagged model and lazy cycle cuts. No additional cycle cuts were needed in the 34 six-centre native refutations. Four complete tagged-CNF refutations have been archived and replayed.

`scripts/coverage.py` generates `lean/FamilyCoverage.lean`, using the repository's restricted-growth-string enumerator from `upstream/WindowAutomatonDefs.lean`. Run `scripts/build_coverage.ps1` for the three standard-library Lean 4.19 audits. This build uses a fresh output folder and no mathlib dependency.

`scripts/independent.py`, `five_control.py`, `screen_short.py`, and `bank.py` record the independent tests, positive control, shorter windows, and bank scan. `scripts/verify.py` checks the saved positive configurations and cycle cuts, the shape lists, the coverage audits, and evidence boundaries.

## Proof reproduction and diagnostic

`scripts/prepare_support.py` pins the normalization support, and `build_support.ps1` builds it in a fresh directory. `check_bridge.ps1` checks classification and the arbitrary-snake bridge; also run it with `-Modules RunDensity,SnakeRunDensity` for the conditional density statements. `certify.py` generates the numerical certificates; `replay.ps1 -Case N` performs each Lean replay. `optimize_export.py --case N` omits executable copies of proof-data constants while preserving their kernel checks. The published cases 14 and 22 use this option. `archive.py` packs or restores the four published certificates. `verify_proofs.py` audits these completed proofs separately from `verify.py`, which checks the earlier experimental evidence.

The export width is selected from the maximum number of simultaneously live proof clauses. Case 2 exposed an insufficient 13-bit choice; its export was regenerated with 14-bit words. Larger exports remain pending Lean replay and require the corresponding checker variant.

`scripts/six_four_graph.py` gives the conditional diagnostic: 96 extra edges are removed, the saved witness-table mean changes from 287/60 to 1739/360, and the lower-table mean stays 119/29. These are exact saved-cycle checks; there is no global minimum-mean or snake-length certificate.
