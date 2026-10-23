# Distance-three singleton inequalities

Research date: 23 October 2026. Completed local theorems; no new global snake bound.

For a seven-edge segment with directions `(a,b,c,d,e,b,a)` and five distinct coordinates, the singleton counts at its first and sixth internal vertices sum to at least **10**. For `(a,b,c,d,e,b,f)` and six distinct coordinates, they sum to at least **9**. No conditions are imposed on the four intervening counts. Both statements, including the coordinate-permutation step, have passed Lean 4.19 with only the standard three foundations.

## Geometric explanation

The two centres differ in exactly the three coordinates c,d,e. Three opposite corners at each centre are forbidden because they are non-path neighbors of the other centre. For each coordinate outside the incident directions and c,d,e, six further opposite corners form an induced six-cycle. At least one vertex is absent from each cycle. The cycles are disjoint. There are four such cycles for the first pattern and three for the second, giving 6+4 and 6+3.

The maintained paper gives this proof in mathematical notation. No historical novelty is claimed.

## Verification

- Nine new theorem audits passed, including joint two-centre counting, clause soundness and both geometric wrappers with arbitrary distinct coordinates.
- The cores have 246 and 194 clauses, with 3,405 and 1,470 LRAT hints. Only ordinary window, degree, cycle and joint-count constraints are used; no share assumptions or added long-cycle cuts are needed.
- `scripts/geometry.py` independently checks the disjoint six-cycles and verifies all 131 bank paths before inspecting their 956 matching segments. The minimum observed sums are 16 for the 10-bound pattern and 19 for the 9-bound pattern. These are bank observations.
- `scripts/verify.py` checks clause provenance, archive hashes, source/build timestamps, axiom audits and saved graph cycles. `data/verification.json` records the completed checks.

## Diagnostic consequence

The earlier graph keeps four count symbols. One extra symbol is needed only when its direction suffix is `012341`, so the refinement has 70,416 states instead of 44,336. Entries represented by the coarse symbol 6 remain potentially larger than six; pair exclusions are applied only when both relevant counts are below six. No additional excess charge is added, avoiding overlap with the previous three-position correction.

The recorded witness-table cycle changes from 287/60 to 1739/360 after both pair inequalities. Adding the unfinished six-count-four conjecture gives the same recorded mean. The lower-table cycle remains 119/29. Saved means and history consistency have exact finite checks; the minimum-mean calculation and numerical share premises are not a complete Lean proof of a global bound.

## Reproduction and next work

The build reuses the checked support from milestones 28, 31 and 32. Run `scripts/certify.py`, `scripts/build.ps1`, then `scripts/replay.ps1 -Case 0` and `-Case 1`. Archives can be restored with `scripts/archive.py --unpack`. `scripts/geometry.py`, `scripts/pair_graph.py` and `scripts/verify.py` reproduce the controls and audit.

The next mathematical direction is to extend this disjoint-cycle argument to other pairs of internal vertices, or combine its frequency with the exact empty-square charge. The gap between the pair bounds and the bank observations warrants a local sharpness test. The mixed-count lower-table cycle still prevents a global conclusion. This checkpoint does not establish the optimum or improve the integrated interval 191 <= a(9) <= 238.

Milestone34 subsequently found and Lean-checked complete snakes attaining both constants. See [the sharpness checkpoint](../34-distance-three-sharpness/README.md). Stronger unrestricted count-only constants are therefore impossible; the proposed next target uses the empty-square share at equality.
