# Consecutive singleton counts equal to four

Research date: 23 October 2026. This is a new hypothesis and coverage checkpoint, not a completed geometric theorem or a new bound on snake length.

The successive witness-table cycles in milestones 29 and 30 repeatedly use counts equal to four. After two further seven-centre shapes were solver-excluded, the investigation tested the direction-independent hypothesis that a snake cannot have seven consecutive internal singleton counts all equal to four. All 132 normalized induced eight-transition shapes returned UNSAT in the radius-four model. Testing one fewer centre then gave UNSAT for all **34** normalized induced seven-transition shapes.

The resulting stronger hypothesis is:

> No snake in Q9 has six consecutive internal vertices whose singleton-square counts all equal four.

The 34 numerical exclusions remain **solver-only**. Three Lean audits check the finite coverage table: every normalized induced seven-transition pattern belongs to the displayed 34-case list, and every listed pattern passes the normalization and inducedness tests. The geometric refutations of those cases and the passage from an arbitrary snake to a normalized pattern remain separate obligations.

## Controls and limits

- A five-centre all-four local forest was found, checked independently by explicit vertex and square counting, and accepted as a fixed selection by an independent exact-square CP model. This prevents shortening the proposed local-model exclusion to five centres.
- Independent CP checks returned INFEASIBLE for six-centre cases 0 and 33, and UNKNOWN for case 23. Its unconstrained five-centre search initially returned UNKNOWN; the later fixed positive control returned FEASIBLE. All records are retained.
- All 131 saved 191-edge bank snakes were independently rechecked for distinct vertices and all-pairs adjacency, then scanned for count-four runs. Their maximum observed run is two. This is a bank observation, not a theorem for arbitrary snakes.
- Additional four- and five-centre screens are saved under `data/short-*`. The four-centre models all have local positive configurations. Several five-centre cases remain UNKNOWN. No unknown case is treated as an exclusion.
- A local forest can have many components ending at the boundary of the examined region. No extension of a local positive configuration to a complete snake has been established here.

## Files and reproduction

`scripts/screen.py` performs the initial seven-centre screen; `screen_six.py` performs the 34-case six-centre screen. Both save results incrementally. The local test uses the existing tagged model and lazy cycle cuts. The complete tagged CNF refutations have not yet been archived or replayed for these cases.

`scripts/coverage.py` generates `lean/FamilyCoverage.lean`, using the repository's restricted-growth-string enumerator from `upstream/WindowAutomatonDefs.lean`. Run `scripts/build_coverage.ps1` for the three standard-library Lean 4.19 audits. This build uses a fresh output folder and no mathlib dependency.

`scripts/independent.py`, `five_control.py`, `screen_short.py`, and `bank.py` record the independent tests, positive control, shorter windows, and bank scan. `scripts/verify.py` checks the saved positive configurations and cycle cuts, the shape lists, the coverage audits, and evidence boundaries.

The next proof task is to certify the 34 exclusions and combine them with normalization and coverage. Earlier seven-centre results do not by themselves prove this shorter, direction-independent statement. A proof should also be checked for implications of existing shorter exclusions before generating redundant large certificates.
