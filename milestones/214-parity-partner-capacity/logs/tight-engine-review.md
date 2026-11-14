# Round 214 tight-partner engine source review

Independent bounded source review, 15 November 2026. Read the complete new C source and TightPartner214 theorem source, the diff against round212, and the supporting PartnerSubset212 statement/proof. No tests, compiler, solver, worker, or traversal ran. No correctness defect was found in the added matching/filtering logic under the saved model assumptions.

## Required mathematical premises

The family has a common pool of 32 words, distinct assigned words within the chosen list C, distinct assigned words within the outside list O, and complete listed partners for any equality between these two lists. Assignments fit the current domains. The spare capacity is s = 32 - |C|. The saved case22 families have sizes (|C|,|O|,s) = (30,9,2) and (26,13,6).

The C parser enforces valid identifiers, unique and disjoint chosen/outside lists, unique partner identifiers drawn from C, and initial domains contained in the family word mask. It does not verify the mathematical distinctness constraints or partner completeness against the binary tables. Those remain prerequisites supplied by the previously audited prepared model and source-specific geometry. The new function additionally requires exactly 32 pool words and at most32 chosen/outside variables. These checks do not certify arbitrary input files as geometric models.

For any outside subset J, let N contain every chosen partner having a domain intersection with a member of J. PartnerSubset212 gives |J| <= |N| + s. Its hypotheses allow N to overestimate actual partners. If equality holds, every other outside variable must share a word with a chosen variable outside N. TightPartner214 proves this implication by saturating the combined list of N-values and exceptions. The filtering theorem then retains the union of domains of the remaining listed partners. Source inspection found no missing cardinality or distinctness hypothesis in this argument. The parent's separate Lean acceptance is not independently rerun here.

## Matching and explicit subset conditions

At tight_solver.c:69-82, augmentation maintains a column-to-row ownership map. Every unsuccessful recursion leaves ownership unchanged; a successful recursion updates one alternating path. Columns are visited at most once per augmentation, preventing cyclic recursion. Resetting visited columns and rows for each new outside row is correct. The saved matching covers all earlier rows before the next row is inserted.

At lines86-113, real edges represent exactly domain intersections with listed chosen partners. The s dummy columns are universal; they represent spare capacity, without assigning specific unused words. Every actual assignment satisfying the premises admits such a matching: distinct shared outside values have distinct chosen carriers, and at most s unshared outside values use distinct dummy slots. Failed augmentation rejects only after recomputing the union of real neighbours of its visited rows and explicitly verifying the strict capacity violation. Failure of this certificate check exits with error status3; it does not return an exhausted subtree.

At lines115-146, the traversal follows each reached row's columns to their matched owners. Encountering an unmatched column prevents filtering. Otherwise it explicitly checks |J| = |N| + s before any deletion. Rows and neighbour positions are represented as bit sets, so their population counts have no multiplicity. The closure traversal is a discovery procedure; the verified capacity equality and partner coverage justify the deletion. No general assertion that every pool word is used is introduced.

For a row outside J, the retained mask is its old domain intersected with the union of domains of its listed partners outside N. This matches tight_partner_filter_preserves_assignment. An empty result therefore rejects the branch only under the same family premises. A wrong closure cardinality is an error exit, distinct from branch rejection.

## Sequential deletions and propagation

The arrays real and edges are built once per family call. Later filtering can shrink outside domains while those arrays remain unchanged. This is safe: the old neighbour set still contains every currently possible supported partner. The theorem permits this overestimate; equality in its cardinality bound still forces sharing outside that set. Within the call, only outside domains change and the chosen/outside lists are disjoint, so the chosen-domain unions used for support do not become stale. Different family calls rebuild their own graphs from the then-current domains. Even if family lists overlapped across calls, monotone deletions would preserve this reasoning under each family's premises.

Every nonempty deletion sets altered and calls changed(x), placing affected binary arcs back into the existing queue. The next outer propagation pass processes that queue and recomputes the graph. The original binary propagation, nogood filtering, lexicographic filtering, and simpler spare-support filtering are unchanged. Their earlier correctness and symmetry assumptions remain inherited; this review does not expand their scope.

The complete source diff contains only the new counters and two matcher functions, calls after the old support loop, and additional output counters. visit, input parsing, pending-frontier construction, branch order, limits and all old filtering bodies are unchanged. The new failure modes use the existing exit3 path. A continuation runner must treat such exits as execution failures; this source review does not audit the runner or any accepted receipt chain.

## Bounds and C representation

The new masks use uint64_t. The largest explicit shift is BIT(32); chosen and outside positions are at most31. The parser enforces a positive chosen count, and the new function checks count <=32 before constructing masks. All calls to ctzll are guarded by a nonzero mask. owner entries are initialized to -1 and receive only row indices below the outside count; recursion and reached-row shifts therefore stay in range. position is initialized over the valid identifier range, and every partner is validated as a chosen identifier. A visited-column bound also limits augmentation recursion to the small graph. No new signed shift or shift-by64 occurs.

The source comment describing recomputed neighbours refers to unions of saved real-edge masks. It should not be read as claiming that domain intersections are refreshed before each subset. Their monotone overestimate property is the reason the implementation remains sound.

## Evidence limits

This report establishes source-level agreement of the added rules with the stated capacity argument. It is neither a C verification proof nor a completed search certificate. No native result, performance improvement, normalization coverage, global snake bound, or completed traversal is claimed. Full source/object pins, transferred frontier integrity, runtime outputs and linked state transitions require their own records.

## SHA-256 snapshot

- `214-parity-partner-capacity/scripts/tight_solver.c`: `f4cc2de3768b730e3beb0ac152acf25b516cd258c2dfebd8d77155494a745789`
- `214-parity-partner-capacity/lean/TightPartner214.lean`: `dcaea41f05681f174cce6a620fed4dc60d5785edfc47c6ab2d395aadc6c5a8e2`
- `212-spare-support/scripts/spare_solver.c`: `4c1d8c773075ad6b04c05125b7e5b7fb27b26cdbe9c77e6a9be8d2202700acf0`
- `212-spare-support/lean/PartnerSubset212.lean`: `6aba653343e45446833dc1b15968f9dd5b498e8567d2448d88e05dae277c18ce`
- `212-spare-support/lean/SupportBridge212.lean`: `c1f687a0a40499881115d7c48ce1dc638c8980363e36b919b4c1a8cff8810b2f`
- `212-spare-support/data/case-22/support-constraints.json`: `0362c97affd2b4b19405f2a05747327a703b55459b6f1cb3d7bc455c72bce040`
