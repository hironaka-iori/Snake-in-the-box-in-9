# Saved-frontier continuation

This is a written proof review. No compiler, search, or software test was run. The proposed continuation rule preserves coverage. Its native implementation and persistence protocol require the separate checks listed below.

## Fixed meaning of a subproblem

Fix the original geometric constraints, normalization, forbidden tuples, and global lexicographic inequalities. Let an acceptable assignment mean a complete assignment satisfying those fixed conditions. A domain vector represents the acceptable assignments whose values lie in its domains.

All subsequent statements use this same meaning. A resumed domain vector generally is not invariant under the coordinate group. It must retain the original global lex inequalities rather than select a new orbit representative within its restricted domains. Sound fixed-prefix propagation of the original inequalities remains permitted.

## Coverage at a limit

Suppose a call reaches its entry limit before propagation. Saving its current domain vector preserves every acceptable assignment represented by that call. Saving an unpropagated vector can retain unnecessary states, but cannot omit a solution.

At an ancestor, let the already-propagated domain vector be $D$, let $k$ be its chosen variable, and let the current child have fixed $x_k=v$. Before entering that child, the branch iterator must already have removed $v$ from its remaining-value mask. The current child's saved frontier covers all of its unrefuted acceptable assignments by induction. Earlier children have completed exhaustively. If the remaining mask $R$ is nonempty, the additional saved vector

$$
D[k\leftarrow R]
$$

represents exactly the union of all unvisited siblings. It is disjoint from every region inside the current child, since those retain $x_k=v$ while $v\notin R$. Saving this one sibling union and propagating the limit upward therefore preserves all acceptable assignments of the ancestor.

Induction to the original job proves coverage. The saved regions are pairwise disjoint because sibling regions differ at their first separating branch variable, and descendant propagation only shrinks domains. Disjointness also assumes that the incoming committed frontier was disjoint and that each replacement is a subset of its replaced job. Coverage is the essential correctness property; accidental duplicate regions would cause repeated work rather than a false exclusion.

At most one region is saved at each ancestor, plus the entry-limit region. Since branching fixes a previously nonsingleton variable and domains never expand, this produces at most one more saved region than the number of variables. This bound concerns one limit unwind, not the total size of a frontier accumulated across many jobs.

The implementation must save independent copies of all domain entries. Retaining pointers to stack arrays or subsequently modified masks does not establish the stated coverage. Saving the ancestor's complete remaining mask must occur before any additional value is consumed from it.

## Replacing a pending job

An exhausted job has no acceptable assignments and can be replaced by an empty frontier. A limited job can be replaced by its saved covering frontier. Replacing one pending region by a cover preserves coverage of the original problem. Repeated replacements therefore preserve the invariant that every acceptable solution lies in some pending job.

An empty committed frontier implies exclusion only when every retired job has a sound exhaustion or refinement justification. A status string or receipt is evidence to be checked; it is not itself the mathematical soundness premise.

A `FOUND` result does not exhaust the rest of its region. It may terminate a witness-seeking task, but retiring that region cannot support a later global exclusion unless the unvisited parts are separately retained or excluded.

## Interruption and persistence

Keeping the old job pending after a hard kill is safe. Any partial frontier written by the killed process must remain uncommitted, even if some individual entries look valid. An exit reporting a limit is usable only after the complete saved frontier and associated receipt have been validated and persisted.

Persisting a receipt before deleting the old job is necessary but not sufficient for crash-safe coverage. Removing the old job and adding every replacement must be one committed queue update, or the old job must remain available until all replacements are committed. A crash between removal and insertion would lose coverage.

A suitable protocol writes a complete new queue snapshot, including replacement children and identifying the original job, before atomically replacing the committed snapshot. A crash before commitment leaves the old job; a crash afterwards leaves its full replacement. Receipt and frontier data must already be available and tied to the same input. The exact durability claim must distinguish application interruption from operating-system or power-loss guarantees.

A continuation receipt must identify the unchanged model and symmetry constraints, original job, domain dimensions, and complete frontier. Replacing or renormalizing constraints silently would invalidate the coverage induction. Restoring a parent job after an uncertain interruption is conservative; it can repeat work without omitting solutions.

## Lean draft and scope

The accompanying uncompiled `Std`-only draft, `lean/Frontier208.lean`, proves the following abstract statements:

- A product domain splits into its chosen-value region and the region obtained by removing every occurrence of that value.
- The two regions are disjoint.
- Replacing one region in a covering frontier by a covering refinement preserves coverage.
- A frontier with an explicit coverage proof excludes solutions when it is empty.

The remaining-value list uses a filter, rather than removing only the first occurrence, so the disjointness statement does not require a duplicate-free list hypothesis. Native bitmasks already have unique values.

The generic coverage lemmas apply to regions intersected with the fixed acceptable-assignment predicate. They do not verify native pruning, the depth-first unwind, saved vectors, receipts, atomic file updates, or a concrete finite exclusion. Those obligations remain separate from the abstract Lean statements. Native source review will be added only after the implementation is available and inspected.
