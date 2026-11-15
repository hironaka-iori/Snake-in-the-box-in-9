# Actual simultaneous replacement: source preparation

Status: final substantial source repair for this round prepared. The parent has accepted `ReplacementIndices225`, `ReplacementCases225`, `ReplacementPairs225` and the separate optional `EndpointParity225`. Three constructor attempts and two separate ordered-pair theorem attempts stopped at the 256 MiB private-memory limit. No compiler, solver, native worker or software tests ran during the source repairs. The compact hypothesis interface, ordered-pair theorem, constructor and independently extracted enlargement theorem await guarded compilation.

## Constructor hypotheses

`Simultaneous225.replaceTwoBlocks` starts with one actual induced path `p` of edge length `n` and an arbitrary candidate map `q` on the same indices. It does not assume that the complete candidate is injective or induced. The ordered anchors satisfy `a<=b<=c<=d<=n`, permitting degenerate intervals as well as the intended positive-width cuts.

The required facts are:

1. The candidate agrees with the original path outside the two open interiors `(a,b)` and `(c,d)`.
2. On each closed replacement interval `[a,b]` and `[c,d]`, the candidate is injective and has adjacency exactly between consecutive indices.
3. Each new interior is disjoint and nonadjacent to retained vertices strictly outside its own closed interval. A retained vertex lies outside the other open interior. Both edge orientations are excluded, so no ambient symmetry assumption is needed.
4. The two new interiors are disjoint and nonadjacent in increasing interval order.

Own anchors are deliberately excluded from the boundary nonadjacency premises. Their intended edges and distinctness are supplied by the local closed-interval path hypotheses. Agreement fixes all anchors, including a shared anchor when `b=c`. The two open interiors have index separation at least two even in that touching-anchor case, so mutual nonadjacency does not forbid a required path edge. Empty interiors and one-edge replacements are covered.

## Proof

The proof first establishes both distinctness and the exact edge relation for every ordered pair of indices. Pairs lying in one closed replacement use its local hypotheses. A pair crossing the two new interiors uses mutual separation. A new-interior/retained pair outside the local closed interval uses boundary separation and the outside-agreement identity. All remaining pairs retain the original path's vertices and use its actual induced-path properties. Index arithmetic proves that every pair handled by a separation hypothesis is nonconsecutive.

The ordered-pair result supplies full injectivity by comparing indices in either order, and supplies the induced field directly. The returned path has vertex map exactly `q` and unchanged edge length `n`. No intermediate one-block replacement is assumed valid: the two new interiors may each contact the other block's old vertices, which have been removed simultaneously.

The complete accepted `BlockReplacement193` replacement proof was inspected in the preceding round. The present construction follows its boundary-pair reasoning while adding the simultaneous new-interior case. It uses the accepted `LayerJoining` and `ReplacementIndices225` modules through two further small proof modules, adds no mask or graph definitions, and makes no numerical closure or existence claim.

## Enlarging the search intervals

`agreement_of_enlarged_intervals` proves the additional inclusion fact: if `a'<=a`, `b<=b'`, `c'<=c` and `d<=d'`, agreement outside the two short open intervals implies agreement outside the corresponding enlarged open intervals. An index outside an enlarged interior is outside the contained short interior; the original agreement hypothesis applies. The same maps and global path length are retained. Endpoint equality in interval containment is allowed and causes no anchor error.

This lemma establishes agreement monotonicity only. Using a saved wider-context exclusion for a narrower search still requires the same actual candidate, global target and all other model premises. It does not itself certify the 44 wider contexts, contact restrictions or native search completeness.

Two main axiom reports are requested. Their acceptance, concrete local certificates, native interval enumeration and any longer witness remain pending separate verification.

## Source repair after the memory stop

The failed source and execution plan were copied into `logs/simultaneous-repair-1`. Its `manifest.json` also pins every unchanged file in the original compiler-run directory, including the empty compiler log and failed execution record. The initial source hash is `b002d76d8b2c98824adf70c4c266b9dbc7e5a30a5678e0d8c3233165b0a2661d`. The archive-manifest hash is `ad3bd03f16a68a6f0452a06a133c1fd0131e4823aa1d1b91170f6f1a633ca3c2`.

The repair preserves the complete constructor and enlargement theorem statements. All arithmetic tactic calls were removed from the constructor. Six elementary natural-number facts now reside in `ReplacementIndices225.lean`, where the arithmetic tactic sees only a few inequalities and no path, relation, agreement or separation functions. Basic transitivity and inequality facts replace the local injectivity arithmetic. This isolates the suspected elaboration cost; an improved memory result has not yet been measured.

Compilation order is `ReplacementIndices225`, then `Simultaneous225`, using the existing preparation and guarded checker for each. The helper requests six axiom reports; the main source requests two. No execution plans were regenerated during the repair.

Prepared source hashes:

- `ReplacementIndices225.lean`: `69a50aa3aa3900d31f95ff68a9256405f9d908705b67241959b59cd07bc599fd`.
- `Simultaneous225.lean`: `2cee2bb8fe0918cc19d1c036ac45ac9021058043123a011f71a5a14e1430dbca`.

## Second source repair: separate interval classification and pair verification

The first repair did not solve the constructor's memory problem. Its failed source and execution plan are copied into `logs/simultaneous-repair-2`, and the manifest pins the unchanged second compiler log, record and snapshots. Manifest SHA256: `0fb61460dcc0b31175a34fd9374d48c29c5544fc75b1d5a67a6ec2c51e4fa8e3`. The accepted arithmetic source remains unchanged.

`ReplacementCases225.classify` proves the exhaustive eight-way classification of an ordered pair of natural-number indices: both in either closed interval; in the two separate interiors; an interior followed by retained indices in either interval; retained indices followed by either interior; or both retained. Every nonlocal case includes a proof that the indices are nonconsecutive. This module contains no vertex map, adjacency relation or path assumption.

`ReplacementPairs225` contains five small proofs for local injective induced pairs, separated pairs, retained vertices on either side, and two retained vertices. Each is checked independently as a declaration. The public constructor now applies the case classification and calls these pair lemmas in eight short branches. Its complete statement, returned vertex map and interval-enlargement theorem remain unchanged. The new sources introduce no extra definitions or axioms.

Next guarded compilation order, reusing the accepted arithmetic object:

1. `ReplacementCases225` (one requested axiom report).
2. `ReplacementPairs225` (five reports).
3. `Simultaneous225` (two reports).

Current prepared hashes:

- `ReplacementCases225.lean`: `c4ef95aca7270e7bc7b36a434be78f631dc6696b8a64e108e5ebc18c078bbaf7`.
- `ReplacementPairs225.lean`: `e88a8c6d12037011fd63036d016ffb18ed89035b1e158f3b2860bc084c5fbb5a`.
- `Simultaneous225.lean`: `4980e315fc84bb77d1de69615402875fd105e11858c0d3ad96872640b3a2341e`.

This split has not yet been compiled, so no memory improvement or constructor acceptance is claimed.

## Third source repair: separate theorem from the path-valued definition

The parent accepted `ReplacementCases225` in 1.062 seconds and `ReplacementPairs225` in 1.063 seconds. The composed constructor still exceeded the memory limit, so the entire ordered-pair proof is now a top-level proposition-valued theorem in `ReplacementOrdered225.lean`. Its hypotheses are precisely those already supplied to the constructor, followed by the two indices and their strict order. No path property of the candidate is added as an assumption.

The constructor imports this theorem and builds the structure using `where`, with `vertex := q`. Its injectivity field applies the ordered-pair theorem in either index order; its induced field is the theorem's second conclusion. There is no large local proof declaration inside the path-valued definition. The public constructor type and interval-enlargement statement remain unchanged. Code-generation expansion of a large local proof is a possible source of the repeated peak, but this is a diagnosis to check, not an established cause.

The third failed source and execution plan are copied into `logs/simultaneous-repair-3`; the manifest pins the original failed log, record and snapshots. Manifest SHA256: `83509a68bae6e5762131fa3ef463918c0693a5aebc9d51a86f6da3f9ffbc9d12`.

Compile `ReplacementOrdered225` first (one report), then `Simultaneous225` (two), reusing all accepted dependencies. No compiler was launched during this preparation. Current source hashes:

- `ReplacementOrdered225.lean`: `33080313b46c72016cadf8a5d9058f3ca44ef3dc0a546e16c5636971ecea002a`.
- `Simultaneous225.lean`: `84bc98cbf3e964c205dd3ce7bf4abb710f1ed94c7e3ff5b5697eab045daf0077`.

## Fourth source repair: explicit disjunction elimination

The separately compiled ordered-pair theorem also stopped for memory after 1.109 seconds. This rules out the final path record being the sole source of the previous failures. The failed ordered-pair source, execution plan and original compiler evidence are preserved under `logs/simultaneous-repair-4`, with manifest hash `bd60e77f59d1e037bf6eef2a634a75603aedf3a98f194d7e98620038c7568da4`.

The theorem now uses a term-mode chain of `Or.elim` applications instead of `rcases` in the full hypothesis context. All graph, vertex, dimension and index arguments of the generic pair lemmas are explicitly supplied. The proof still follows the same eight exhaustive cases and the public theorem type is identical. No accepted helper or constructor source was changed in this repair.

Prepared ordered-pair source SHA256: `caa75aea8608331c95bd78ef3417e1fd45e5b478fef263884a6fe03179065ab8`. Compile this module, then the unchanged constructor. The effect on elaboration memory remains unmeasured.

## Fifth source repair: one internal proposition containing the local premises

The explicit proof-term attempt also stopped for memory after about 1.11 seconds. Its source, execution plan and original compiler evidence, together with the previous constructor source, are preserved under `logs/simultaneous-repair-5`. Manifest SHA256: `4a0e523ba094a67467646a2ac359cedf7e0de919afd3a4b6c14571128e439ae1`.

`ReplacementConditions225.Conditions` is an internal proposition structure containing exactly the nine previous hypotheses: ordered anchors, outside agreement, two local injectivity statements, two local induced-adjacency statements, two retained-boundary separation statements, and mutual-interior separation. Its constructor packages these facts and its projections recover each one. Neither global injectivity nor global inducedness of the candidate is a field. This changes the Lean interface while preserving the mathematical assumptions.

`ReplacementOrdered225.ordered_pair` now accepts this one proposition instead of the nine separate function hypotheses. Its proof retains the explicit eight-case disjunction elimination. `Simultaneous225.replaceTwoBlocks` accepts the same compact interface and constructs the actual path with vertex map `q`. No compatibility wrapper or new arithmetic definition was added.

The interval-enlargement theorem was extracted unchanged into `IntervalEnlargement225.lean`, under its own namespace. It imports only the accepted arithmetic helper and can be checked independently of the constructor. The main constructor module now requests one axiom report instead of two.

Next checking order: `IntervalEnlargement225` independently; then `ReplacementConditions225`, `ReplacementOrdered225`, and `Simultaneous225`, one requested report per module. All previously accepted sources remain unchanged. If the constructor route again exceeds the limit, the correct status is that its assembly remains unchecked; the accepted helper and parity results must be reported separately.

Current prepared hashes:

- `ReplacementConditions225.lean`: `326d847ba613a6f335ca1c236a0207295af082ecacbb3d4a8ff3ab56d1fb891c`.
- `IntervalEnlargement225.lean`: `ba5dd0ccf2a509b3891988f719bc3fbc779c297f271cd7fd3dffd9628a21644d`.
- `ReplacementOrdered225.lean`: `2f52a7a5c62e05cf0d5991202f0c2a093bc9519857ca8e61ce37d05a6c1e785a`.
- `Simultaneous225.lean`: `ce2129459ff1cc31f2cce81c599a0c7c25bc31fb07dac3c5aded95ccadf71882`.
