# Nine-dimensional snake-in-the-box investigation

Research checkpoint: 14 October 2026.

The authoritative evolving paper is [`snake9_research.tex`](snake9_research.tex), authored by Iori Hironaka. It is compiled in the document editor. The existing exported PDF and full research bundle are earlier snapshots and do not contain the latest revisions. The paper includes prior observations, the hypothesis, mathematical proofs, search evidence, explicit witnesses, references, and verification limits. Lean implementation details are kept outside the manuscript.

**New written refinement:** a square-face argument gives `a(9) <= 254`. The local singleton-square lemma is now Lean-checked for every path length and vertex. Its global incidence counting still awaits Lean verification. `SquareCountingLogic.lean` checks the arithmetic deduction from explicit census premises only. `SquareCounterexample.lean` fully verifies a 137-edge path refuting the universal two-singleton-square condition for internal vertices of open snakes. See [square-face investigation](square_investigation.md).

**Global Lean-checked bounds:** 191 ≤ a(9) ≤ 255. `SpectralUpperBound.lean` derives the upper bound from the maintained Lean proof of Huang's degree theorem and connects it to the same integer-based `Snake9.Snake` definition as the witness. See [spectral verification](spectral_verification.md). The mathlib-dependent extension has its own archive, `snake9_spectral_project.zip`; the core archive remains standard-library-only.

**Revised working conjecture:** the maximum induced-path length in the nine-dimensional binary cube is 196 edges, based on the pattern in the first eight exact values. This is a low-confidence extrapolation, explained in [the trend analysis](trend_hypothesis.md). **Status:** a lower bound of 191 is verified in Lean; no 196-edge construction or matching upper bound has been obtained. No 192-edge counterexample was found in the searches described below. The earlier candidate optimum of 191 remains under active challenge.

A vertex of the cube is a binary word of length nine. An edge changes exactly one bit. A snake is a sequence of distinct vertices in which exactly the consecutive pairs are adjacent. A snake with 191 edges therefore has 192 vertices.

## Source and independently verified evidence

The starting work is Orland et al., [New Snake-in-the-Box Records via Snakepit Surgery and Learned Construction, version 3](https://arxiv.org/html/2607.15270v3), dated 30 September 2026, and its [public dataset](https://github.com/Math-AI-Caltech/Snake-in-the-Box). The paper supplies a 191-edge construction and explicitly leaves nine-dimensional optimality open. Its 131 examples form a discovered collection, without a proof that the collection is exhaustive.

Independent checks in this investigation established the following:

- The example from Appendix E has 192 distinct vertices. All 18,336 unordered vertex pairs satisfy the induced-path condition. Lean also verified this witness.
- All 131 nine-dimensional dataset entries pass a separate Python check, including agreement between transitions and vertex lists. This checks 2,402,016 unordered vertex pairs in total.
- The 131 entries are inequivalent under translation, coordinate permutation, and path reversal, as checked by canonical transition sequences.
- Every entry is blocked against adding one vertex at either endpoint. These dataset-wide checks were performed in Python, not in Lean.

The exact downloaded dataset archive is identified by SHA-256 in `snake9_bank_audit.json`.

## What Lean proves

The core project uses Lean 4.19.0 and its standard library. The separate spectral extension uses pinned mathlib. The finite witness checks use `by decide`, checked by the Lean kernel. No theorem uses `sorry`, `admit`, an optimality axiom, or `native_decide`.

`Snake9.lean` defines vertices as `Fin 512`. Adjacency means that one of the nine individual bit flips transforms the first vertex into the second. The theorem `adj_iff_coordinate_flip` checks that the executable adjacency definition has precisely this meaning.

`Snake m` requires an injective vertex sequence of length `m + 1`, with adjacency exactly between consecutive indices. The checked results include:

| Result | Meaning |
|---|---|
| `lower_bound` | A 191-edge snake exists in the nine-dimensional cube. |
| `takePrefix` | Every initial segment of a snake is a snake. |
| `no192_iff_upperBound` | Absence of a 192-edge snake is equivalent to the universal upper bound of 191. |
| `target192_iff` | The explicit 193-vertex feasibility statement is equivalent to existence of a 192-edge snake. |
| `optimality_of_no192` | The witness is optimal **if** that feasibility statement is false. The premise is unproved. |
| `witness_right_blocked` | The Appendix E witness cannot accept an extra vertex at its right endpoint. |
| `all191_blocked_implies_optimal` | Blocking the right endpoint of **every** 191-edge snake would prove optimality. The universal premise is unproved. |

The axiom audits contain only `propext`, `Quot.sound`, and, in the general joining module, `Classical.choice`, standard logical foundations used by Lean. They do not contain `sorryAx` or `Lean.ofReduceBool`.

## A checked objection to an invalid proof strategy

A separately constructed snake has **93 edges** and cannot be extended at either endpoint. `MaximalityCounterexample.lean` verifies its distinct vertices, all its adjacency conditions, and explicit blockers for all nine candidate moves at each endpoint. It also verifies that the second orientation is the reversal of the first.

The general theorem `blocked_prevents_extension` proves that these blockers prevent a genuine one-edge extension of the same path. Together with the verified 191-edge example, this gives a concrete counterexample to the inference that a snake blocked at both endpoints must have maximum length.

This is a counterexample to the proof strategy. It is **not** a counterexample to the conjectured value 191.

## The earlier 191-optimality target

The following target concerns the earlier candidate optimum 191. The revised 196 hypothesis instead requires a 196-edge witness and exclusion of a 197-edge snake, as checked in `OptimalityTarget.lean`.

Let a hypothetical longer snake have vertices

\[
v_0,v_1,\ldots,v_L,\qquad L\geq192.
\]

Its first 193 vertices form a snake of exactly 192 edges. Consequently, proving optimality requires excluding precisely that finite target:

\[
\nexists\,(v_0,\ldots,v_{192})\in(\{0,1\}^{9})^{193}
\]

with distinct vertices and

\[
d_{\mathrm H}(v_i,v_j)=1
\quad\Longleftrightarrow\quad
|i-j|=1
\qquad(i\ne j).
\]

Lean checks this reduction. It does not prove the nonexistence statement.

There is also a completeness route. If every 191-edge snake were equivalent to one of the 131 blocked examples, a hypothetical 192-edge snake would have a 191-edge prefix in that collection. The final vertex would extend it, contradicting the endpoint check. The missing premise is the completeness of the collection. Repeated recovery of the same examples does not establish that premise.

## Counterexample searches and their limits

An unrestricted exact constraint model was implemented for the 192-edge target. It selects cube vertices, forces every cube edge between selected vertices to belong to the path, and uses a single circuit through an auxiliary vertex to enforce one connected path. Removing the auxiliary vertex leaves the required induced path. Translation fixes the first vertex at zero. Coordinate permutations fix the first two moves and order the remaining coordinate-use counts; these reductions preserve a representative of every snake of the target length.

The model reproduced the feasible/infeasible thresholds in dimensions three, four, and five. In dimension nine it accepted the known 191-edge witness and excluded adding a single vertex while retaining every vertex of that witness. These controls increase confidence in the implementation; they do not constitute a Lean proof of the solver implementation.

The unrestricted run used four solver workers and a 300-second limit. Its result was **UNKNOWN**, after approximately 300.2 seconds, 1,040,308 reported branches and 37,810 reported conflicts. This is neither a counterexample nor an impossibility certificate.

Separate depth-first searches exhaustively tried endpoint regrowth for every published example in both orientations:

| Terminal vertices removed | Prefix vertices retained | Completed exclusions | Unresolved searches | Search nodes |
|---|---:|---:|---:|---:|
| 32 | 160 | 262 | 0 | 488,450 |
| 40 | 152 | 262 | 0 | 16,561,030 |
| 48 | 144 | 209 | 53 | 66,968,134 |

Each search targeted 193 total vertices. The 48-vertex runs had a one-million-node limit per orientation; reaching that limit was recorded as UNKNOWN. Thus every 152-vertex prefix obtained from either end of a published example is excluded as the beginning of a 192-edge snake by this exhaustive Python search. This says nothing about prefixes outside that restricted collection. The regrowth computations have not been verified in Lean.

## Independent counterexample route

A new vertex-set neighborhood model allows both endpoints and internal segments to change. For each of the 131 published examples, it excluded a 192-edge target retaining at least 190 of the 192 seed vertices. All 131 runs returned INFEASIBLE, in about 241 seconds total. These solver exclusions lack Lean certificates. Allowing eight removed vertices returned UNKNOWN for the first three seeds at 30 seconds each. The files `neighborhood_2.json`, `neighborhood_8.json`, and `neighborhood_controls.json` preserve the results and controls.

The competing hypothesis is that a 192-edge snake exists outside the published collection. One sufficient construction would be an induced cycle with 194 vertices. Deleting one vertex would leave 193 vertices and 192 edges in an induced path.

`CoilReduction.lean` checks the general deletion construction and the theorem `coil194_disproves_191`. No 194-vertex cycle is assumed to exist. Four structured cycle searches were attempted; all returned UNKNOWN. The additional generators had weights 2, 4, 6 and 8, with time limits of 120, 60, 60 and 120 seconds respectively. A small control instance produced a 14-vertex induced cycle and passed direct pairwise validation. These are additional attempts at finding a counterexample, not proofs that one exists or is impossible.

## Testing the revised hypothesis through eight-dimensional layers

`LayerJoining.lean` proves the necessary and sufficient intersection condition for joining induced paths across one binary coordinate. `Snake8.lean` verifies the published 98-edge seed. `IntegerLayerBridge.lean` now proves the injective encoding and adjacency equivalence connecting the layer construction to `Snake9.Snake`. Compatible 98- and 97-edge paths give a 196-edge snake; compatible pairs of 98-edge paths give a 197-edge snake. These are checked construction theorems with explicit compatibility premises; no such pair has been found.

The fixed-seed construction search examined 322,560 placements of a truncated isometric copy; the minimum overlap was 15 vertices, whereas one is required. A broader constraint search excluded every 97-edge partner at either endpoint of this fixed seed. These exclusions are computational results without Lean certificates, and do not cover all 98-edge seeds or general nine-dimensional snakes. See [the layer investigation](layer_investigation.md) for the precise scope.

## Reproduction

For the source repository, use Lean 4.19.0, enter `work/final_lean`, and run:

```text
lake build
```

The source files contain axiom-audit commands, and `lean-build.log` records the clean integrated build. The repository includes witness data, audit summaries, and search programs; see the root README for reproduction instructions. ZIP files mentioned in older notes are local archival snapshots and are not required.

**Research status:** 191 is a verified lower bound; 196 is the revised sequence-based hypothesis. The investigation found no 192-edge snake and did not prove that none exists. The local-maximality argument has been decisively refuted by a Lean-checked example in the same dimension. The additional trend model and the exact proof obligations for 196 are checked in `TrendHypothesis.lean` and `OptimalityTarget.lean`; these files do not prove the geometric conjecture.
