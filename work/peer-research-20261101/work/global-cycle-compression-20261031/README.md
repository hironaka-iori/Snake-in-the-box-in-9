# Q9: remove a spurious critical cycle history before seeking the next upper bound

Local research update, 31 October 2026. Nothing in this round is uploaded. No new global numerical upper bound or Lean verification is claimed.

## Main advance

The upstream proof-supported comparison model's displayed mean-480 four-cycle cannot be repeated as a true snake history. Seven consecutive model edges around it force fifteen literal cube transitions and a chord. This is a direction-only geometric exclusion, with no new singleton-count premise. It targets a concrete equality obstruction in the current potential argument rather than merely improving a bank-prefix search.

The four source edge IDs are 3416157, 1822955, 734195, 4462580. Their ordered weight sum is 1920. The four nine-direction labels and source counts are frozen in upstream_proved_analysis.json. These are the actual upstream checkpoint data, not a fabricated example. The file itself states that the complete arbitrary-snake graph interpretation remains pending; this update does not discharge that outstanding upstream bridge.

## Complete geometric argument

Each consecutive nine-direction word overlaps the next in eight directions. In all four phases, the overlap contains all six labels appearing anywhere in the successor word. An injective renaming into physical cube coordinates is therefore uniquely determined by the overlap. No fresh coordinate can replace an already constrained label. Starting with an arbitrary embedding of the first word in Q9 gives the same Hamming relations up to a cube isometry.

At phase zero the literal directions are the repetition of

    0 1 2 3 4 2 1 5

Seven model edges supply 9+6=15 literal directions:

    0 1 2 3 4 2 1 5 0 1 2 3 4 2 1.

Their XOR is 32, a unit vector, hence the vertices at path indices 0 and15 are adjacent although nonconsecutive. All four phases have the same obstruction (unit masks32,32,8,4 in their own initial labels). The independent program also checks every vertex pair: only (0,15) violates distinctness/inducedness by that point. The first fourteen transitions are an induced path, so this argument does not justify deleting one edge, banning a single four-edge tour, or banning a six-edge occurrence.

The general underlying lemma is elementary: two full copies of any literal direction period p cancel under XOR. For p>=2, the first 2p-1 steps have XOR equal to the last removed unit direction, causing a chord at path distance at least3. Canonical state periodicity alone does not imply literal coordinate periodicity; the unique overlap reconstruction above is the essential extra step.

## Small state extension

Track the consecutive number r of marked cycle edges. On marked edges set r:=r+1; reject the seventh. On every unmarked edge reset r:=0. Only four original source vertices need extra copies r=1,...,6: at most24 extra vertices, taking1,601,856 states to1,601,880. Every old weight is inherited through the projection.

For this exact marked subgraph, membership runs follow the one four-cycle, so the rule is exactly the four forbidden seven-edge patterns recorded in attaining_cycle_review.json. Parallel unmarked edges, exits, returns and self-loops reset the run and remain allowed. An arbitrary-snake walk already known to have these physical direction labels lifts with r<=6, by the geometric proof. The complete upstream walk map remains a separate obligation.

If the old potential inequality at mean480 is valid, pulling it back through the projection preserves every inequality and its range578. It supplies no strict improvement by itself. Other critical cycles may survive. A toy graph demonstrates both possibilities: its unique old mean480 cycle becomes acyclic and, with a costly escape, the toy mean becomes720; adding an untouched480 cycle keeps the minimum at480. Neither toy number is reported as a new upstream mean.

## Exact numerical target

Conditioned on the upstream edge-count formula

    m <= (1098960*d + 8*p + R)/(p + 4200*d),   mu=p/d,

the next desired result m<=234 requires the strict inequality

    227*p > 111960*d + R.

For d1,R578, this means mu>112538/227 (about495.762115). Integer mean496 suffices only with its actual certified range R<=631; the old range must not silently be assumed for a new potential. Mean480 cannot exclude235 even at range0. The independently reviewed arithmetic includes exact scaling, rounding and endpoint caveats in aggregate_review.md.

Thus the work has produced a rigorously justified extra history constraint aimed at the old equality obstruction. It has NOT yet produced the new mean/range certificate needed for a smaller global bound.

## Checks and limitations

- Four exact phase reconstructions and all-pair geometry: PASS.
- 9,837 short-period XOR controls: PASS.
- 825 standard-library toy walks and exact cycle-mean toy controls: PASS.
- Independent branching/parallel/self-loop review:15,840 walks and65 outgoing-state checks PASS.
- Full4,957,613-edge NPZ graph transformation and mean computation: NOT RUN. The graph build artifact is not locally available; the 6.38-MB frozen-critical-edge download did not complete and no coverage of its other components is claimed.
- apply_npz_lift.py: static-reviewed adapter; actual execution BLOCKED because Windows application control blocks the local NumPy extension. test_npz_adapter.py records no passing result. Do not treat this adapter as integration-tested or silently substitute a toy graph for the real source.
- Fresh Lean proof: NOT DONE. Source provenance/ordinary mathematical proof and Python checks are separate from Lean kernel verification.

The weighted overlapping-claw dual in aggregate_review.md also improves the earlier derivation's bookkeeping: nonnegative rational pattern weights are safe when their sum at each residual vertex is at most1, giving omissions at least the ceiling of weighted losses. Independent prefix losses still cannot simply be summed across all snake windows; repeated charging of the same omitted vertex must be controlled globally.

## Reproduce

From this directory with Python3.12+, without -O:

    python check_attaining_cycle.py
    python history_lift.py
    python check_aggregate_review.py
    python review_lift_stdlib.py

The historical independent source hashes are in the JSON receipts. NPZ source identity is frozen by upstream_proved_model.json's complete per-array SHA256 values. If the actual upstream graph has been regenerated in a permitted NumPy environment:

    python apply_npz_lift.py /path/to/proved-graph.npz /path/to/lifted-graph.npz

This builds only the modified graph and its row projection; it does not compute or certify the new minimum mean or global bound. Rerun the upstream exact-potential verification after the lift and retain the new range and complete snake interpretation.

make_cycle_figure.py recreates SVG/PNG, requiring Pillow and Segoe UI for the PNG preview. build_report.py recreates the five-page PDF, requiring ReportLab and SimSun. Full proof steps, figure code, independent controls and data are included in the local ZIP. No solver executable, credentials or downloaded third-party paper PDFs are included.

Upstream references:
- https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/main/milestones/72-four-count-proof-closure/README.md
- https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/main/milestones/72-four-count-proof-closure/data/proved-analysis.json
- https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/main/milestones/72-four-count-proof-closure/data/proved-model.json

No novelty priority is claimed for the general periodic-word lemma or finite-history automata. The specific advance is the independently checked realization obstruction for this checkpoint's exact attaining cycle and its compact proposed integration.
