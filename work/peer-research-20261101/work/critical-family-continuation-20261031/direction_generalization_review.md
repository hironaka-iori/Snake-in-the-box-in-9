# Direction-history generalization: independent review — 2026-10-31

The generalization is sound for Q9: every forbidden edge-ID history whose proof used only its canonical direction windows can be replaced by the corresponding sequence of canonical nine-direction WORDS. It is then forbidden regardless of count labels, source edge IDs, history fields, weights, or graph component membership. This is a stronger universally necessary geometric condition, not a new numerical bound.

The old 222-ID version remains correctly reviewed under its original narrower language. This document does not rewrite that artifact or its review.

## Why the proof generalizes

For a sequence W1,...,Wk of canonical nine-direction words, define a realization to be literal cube-coordinate directions d1,...,d(k+8) such that each sliding nine-direction window canonicalizes to its corresponding Wj, and the resulting cube path is induced. Initial vertex translation and coordinate permutation let us fix the initial window to its own canonical coordinate labels without loss. Then all nine possible next coordinates must be considered; a forgotten historical coordinate is permitted whenever the overlap allows it. If the complete realization set is empty, no Q9 snake contains this word sequence.

Our previous full-coordinate checker for the222 histories read only the direction words. It never used their counts, weights or edge IDs except to retrieve those words. Thus replacing an ID with another edge having the same canonical word preserves every realization constraint and the resulting contradiction. A later graph can enforce the rule whenever its symbols represent these same canonical nine-direction words and its paths correspond to consecutive sliding windows. This does not require a transfer of source edge numbering. The proof is Q9-specific where it enumerates nine literal coordinates; do not assume validity in higher dimensions without rerunning or proving the corresponding dimensional result.

## Independent checks and data

`review_direction_generalization.py` verifies that every retained record's nine-direction word is canonical, projects the222 ID patterns, and deduplicates them into111 distinct word patterns. It independently checks every such pattern by all-nine-coordinate enumeration, full-window canonicalization and full-path inducedness checks, with no fresh-coordinate symmetry or state deduplication. All111 have empty realization sets. The verification requires480,528 coordinate trials.

Artifacts: `direction_patterns_independent.json` and `direction_generalization_review.json`. The original222 pattern SHA256 is `da0b56091dd32d2f8ece68e73cd11e2178a63dec37a63ee9f6bbbd3cad5ca243`; the projected111-pattern SHA256 is `9b624b5f5bc740934446d533a660e963b0d2cf0764c866d7da4c862881a25476`.

A further exact language simplification removes any forbidden pattern containing another strictly shorter forbidden pattern as a contiguous substring. Such removal cannot change the accepted language: avoiding the shorter pattern already avoids every occurrence of the longer one. There are63 substring-minimal patterns, stored separately in `direction_patterns_minimal_independent.json`. This optional simplification does not add or conjecture any exclusion. Keep the full111 list for provenance if the production implementation uses it.

## The universal A/B nine-word rule

Let

    A = [0,1,2,0,3,2,4,3,5],
    B = [0,1,2,3,1,4,3,5,4].

Both word histories

    A,B,A,B,A,B,A,B,A
    B,A,B,A,B,A,B,A,B

are in the checked111-pattern set and have no induced Q9 realization. The exhaustive frontier proof was previously checked in every phase of three small cycles: each has possible sixteen-transition realizations, but none after seventeen transitions (nine graph windows). This rule concerns only direction words, so it applies to all count variants of A/B.

The surviving ten-edge mean480 cycle in `surviving_cycle_geometry_probe.json` has word sequence [A,B] repeated five times. Therefore any nine consecutive windows in its directed repetition match one of the two universal forbidden histories. A direction-history lift must eliminate this repeated cycle, although the ID-specific lift correctly allowed it because its count-dependent edge tokens differed. This identifies the cause of the earlier finite-model obstruction without invalidating the earlier narrower computation.

Do not forbid an individual A edge, B edge, or a single A/B pair: both shorter directions and sixteen-transition realizations exist. Do not assume a fixed literal coordinate period; these A/B overlaps introduce new labels and require complete coordinate branching. No unproved claim that transition17 requires a tenth new coordinate is needed for the finite exhaustive result.

## Required change to the lift construction

For ID patterns, a nonempty prefix ended at one fixed original graph vertex. For direction-word patterns, the same prefix can end at many original vertices because counts/history variants share direction words. Therefore `(prefix)` alone is insufficient as a lifted state, and the old one-prefix-one-endpoint compression is invalid here.

Use state `(original vertex v, AC suffix state q)`. Begin at `(v,empty)` for every original start vertex represented by the graph, and perform a complete reachable-state exploration. For EVERY original outgoing edge e from v, feed its canonical direction-word token into AC. If the resulting state is bad, omit that transition. Otherwise add a lifted edge with the unchanged original weight/projection and target `(target(e),new_q)`. Multiple original edges with the same word remain separate weighted/projection alternatives. Empty suffix states and failure-link suffix matches are essential. Any exploration budget cutoff must mark the construction incomplete; silently dropping unexplored states would make a false exclusion possible.

Correctness follows by induction: every source walk avoiding the checked direction patterns has its unique AC run, hence a lifted walk, while every lifted walk projects to an avoiding source walk. Original graph endpoints and AC suffix must both agree; suffix-equivalent histories may merge only at the same original vertex. Reachable sparse exploration is a construction optimization, not a weakening of this product-state invariant.

One may pull back a valid source potential along the original-vertex projection to certify the existing mean lower bound, but a strict improvement still needs either an acyclic critical lift plus a verified treatment of all other edges or a fresh complete potential certificate. The old six-component frozen subset remains distinct from the complete current eight-case graph. No current full graph or new global upper bound is certified by the present generalization alone.
