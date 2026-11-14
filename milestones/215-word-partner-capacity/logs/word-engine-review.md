# Round 215 word-capacity engine source review

Result: no source-level defect found in the added word-matching and subset-filtering rules under the saved families' distinctness assumptions. This was bounded source inspection on 15 November 2026. No tests, compiler, solver, search worker, or nested agent was run.

## Reviewed change

Read the added helper and its integration, the complete textual diff against round214/tight_solver.c, and Subset211.lean. The diff adds only distinct_words, its counters, two calls per support family before tight_partners, and output counters. The augmenting helper, previous propagation bodies, parser, branch selection, visit, frontier saving and stopping logic are unchanged.

The helper is applied separately to each chosen list and each outside list. It never combines these into one distinct family. A tight chosen subset therefore removes words only from other chosen variables; a tight outside subset removes words only from other outside variables. Listed sharing between a chosen and an outside variable remains permitted. The saved family sizes are 30 and 9 for even identifiers, and 26 and 13 for odd identifiers; each is below the helper's limit 32.

## Matching and subset justification

At word_solver.c:154-170, graph rows are variables in the supplied list and columns are actual word numbers. Each row's edge mask is its domain at function entry. Reusing augment_partner with owner[64] is correct: that helper indexes columns from the edge mask and assumes no fixed column-array length. Ownership is initialized on all 64 columns. It maintains a covering matching of the rows already inserted; visited columns bound the recursive search and prevent cycles. A failed augmentation makes no successful ownership update.

On matching failure, the function recomputes the current domain union of the reached rows and returns branch failure only when its cardinality is strictly smaller than the number of rows. This is the explicit deficient-pool condition in Subset211.deficient_pool_impossible. An unexpected nondeficient union causes the existing error exit 3, rather than reporting the subtree exhausted. Matching success alone is never accepted as a complete assignment.

At lines 171-203, alternating reachability follows row-domain words to matched owners. Any reached unmatched word prevents filtering. For a closed reached set, the saved domain union must have the same cardinality as the reached rows; that equality is checked explicitly. The current domain union is then recomputed. A smaller union gives an explicit deficiency; an equal-size union is saturated. Removing that union from the remaining rows in the same distinct family follows Subset211.outside_not_mem_pool and pruning_preserves_assignment. Every affected variable conflicts with all reached variables because distinctness is required throughout that one family.

## Earlier deletions and queue interaction

Matching and reachability use the entry-domain masks. Earlier subset filtering can invalidate edges of that saved matching. This does not invalidate the deductions: the old graph only proposes a row subset, and the implementation recomputes its current domain union before using it. The current union is contained in the saved union. A deficient current union correctly rejects; otherwise the explicitly checked equality justifies saturation. Any unexpected growth produces an error exit. Some newly tight subsets can be missed by stale reachability; this affects propagation strength, and the next altered pass rebuilds the graph.

During deletion for one tight subset, only rows outside it are changed, so its selected union remains valid throughout that deletion loop. Each nonempty deletion sets altered and queues affected binary arcs through changed(x). The next outer pass processes those arcs. Each chosen/outside call constructs a fresh graph, and the subsequent partner-capacity calls also rebuild their graphs from current domains. Earlier simple support filtering and later tight-partner filtering retain their own previously reviewed premises.

## Integer and indexing bounds

The helper guards count in the inclusive range 0 through 32. Row bits and owner values therefore stay in positions 0 through 31. Word masks use uint64_t, and ctzll returns positions 0 through 63 only when called on a nonzero mask. BIT(63) is a defined shift of UINT64_C(1); the new helper never shifts by 64. owner has 64 entries, edges has 32 entries, and all 64 ownership slots are initialized. The existing parser supplies unique valid identifiers within each chosen/outside list. The empty-list case performs no graph access or pruning. The bitwise complement in before & ~words is confined by the original domain mask, so it cannot introduce values outside the alphabet.

## Required premises and remaining scope

Both lists individually require pairwise distinct assigned words and domain fitting. The parser verifies identifiers, list uniqueness, chosen/outside disjointness, partner membership and initial alphabet containment. It does not prove assigned-word distinctness from arbitrary input binary tables. That premise comes from the saved prepared model and the source-specific path bridge; the new bridge under preparation was not claimed or audited here. No extra assumption that every one of the 32 parity words is used is required.

The generic Lean statements justify deficient and saturated domain unions under their explicit assignment hypotheses. They do not verify this C implementation, the native mask interpretation, normalization, or the full traversal. Runtime source/object pins, transferred-frontier integrity, receipts and continuation coverage require a separate record audit. No performance gain, completed exclusion, or global snake bound follows from this source review.

## SHA-256 snapshot

- `215-word-partner-capacity/scripts/word_solver.c`: `b9dc79b25ff57219066babfe3f10355823ad10605aa199318826e0cbf558df1e`
- `214-parity-partner-capacity/scripts/tight_solver.c`: `f4cc2de3768b730e3beb0ac152acf25b516cd258c2dfebd8d77155494a745789`
- `211-subset-capacity/lean/Subset211.lean`: `51f8fad00d2a807edcd9a768e1751dac0f0f85eb8241808bf0a3a8d91943ce39`
