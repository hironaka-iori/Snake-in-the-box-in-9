# Review of the four-history native search

Reviewed `scripts/history_search.py` in full, the result records in `data/history-search.json`, and the witness metadata of `data/model-0.json`. No search, numerical model reconstruction, or compiler was run. Read-only file hashing confirmed that the current script and input digests match those recorded in the result file. Individual model-file digests were not all rechecked.

No overconstraint or unsound exclusion was identified in the reviewed search, under its asserted source-path assumptions. All 70 recorded indices, from 0 through 69, have status `EXHAUSTED`, null solution, and six excluded assignments. The file reports total elapsed time of 14.125 seconds. These are inspected native records, not independently replayed results or Lean certificates.

## Model construction

The entry point checks the source with `valid(seed)`, and `model` requires `seed[0] == 0`. The group number increases precisely when consecutive base words agree. For a valid source cube path, these are exactly the block-coordinate transitions. Thus each group is one maximal interval of consecutive base-coordinate transitions, and the source block word is constant within it. The assertions on `original` verify that constancy and the alternating group parities.

Each group initially receives all eight four-bit words of the correct parity. Since the first source vertex is zero, this is exactly the parity restriction derived from translation-normalized targets. There is no restriction to source words or to block isometries.

For every original index pair with base distance $b\le1$, the constructed relation is

$$
(b>0\text{ or }u\ne v)
\quad\text{and}\quad
\bigl[(b+d(u,v)=1)\iff\text{the indices are consecutive}\bigr].
$$

For consecutive pairs this requires equality across a base edge and block distance one across a block edge. For nonconsecutive equal-base pairs it excludes both equality and block adjacency. For nonconsecutive neighbouring-base pairs it excludes equality. Base distance at least two needs no relation; the code verifies that such a pair is not consecutive.

All relations attached to the same pair of groups are intersected. Self-pairs are evaluated on the diagonal and intersected into the group domain. They are not dropped. Row masks restrict the second value to its current parity domain; the search also restricts both variable domains, so the unrestricted row index range introduces no extra restriction or missing legal value.

Setting group zero to word zero and group one to word one is the valid translation and first-block-edge normalization from `model-review.md`. The saved source length ensures group one exists for every four-coordinate partition. The 70 four-element coordinate subsets are enumerated directly by `itertools.combinations(range(8),4)`.

## Binary propagation

The forward table for each group pair is the intersection of all its indexed relations. Its reverse table is explicitly constructed as the transpose. A value is removed only when its row has no intersection with the current neighbour domain. Every such removal is a sound consequence of a binary constraint.

Omitting the immediate reverse arc after revising $(x,y)$ is sound here. A removed value of $x$ had no compatible value anywhere in the current domain of $y$. It therefore could not support any current value of $y$ in the transposed relation. Its removal cannot newly invalidate that reverse arc. Other arcs entering $x$ are enqueued.

Each call begins with all arcs queued. Removals caused by forbidden assignments enqueue every incoming neighbour arc, including the one that might otherwise be omitted after binary revision. Thus that different source of domain reduction is handled correctly. Missing a propagation opportunity would ordinarily weaken pruning; no such omission is needed for the present soundness argument.

## Forbidden assignments

Each forbidden tuple denotes one entire variable assignment, rather than a partial pattern. If one of its values has already left its corresponding domain, the tuple is already impossible and the code skips it. Otherwise, when all domains are singletons, the current assignment equals the forbidden tuple and is rejected. With exactly one nonsingleton domain, every other variable is forced to its forbidden value, so deleting that last forbidden value is sound. With multiple nonsingleton domains, the code makes no deletion from this tuple.

The generated exclusions have explicit global-isometry witnesses. `fixed` matches the required base histories to input coordinate histories, and its injectivity is asserted. The remaining input coordinates are permuted bijectively onto the block coordinates. The resulting `mapping` is therefore a full coordinate permutation. The reverse branch first reverses the source and translates its new initial vertex to zero. Each listed image is thus cube-isometric to the source, possibly with path reversal. Additional assertions check validity, the canonical class, domain membership, and all binary constraints.

Choosing only the first matching column with `columns.index` could make an exclusion generator incomplete if duplicate coordinate histories were admitted. It cannot make one of its accepted permutation witnesses invalid, and incomplete isometric exclusions would not invalidate an exhaustion result: the search would still have had to exclude every remaining assignment. Completeness of the forbidden list is not a premise of the no-new-class conclusion.

The sampled model zero contains six forward witnesses. This review did not separately inspect every model's orientation flags, so the general conclusion retains the script's convention allowing reversal unless the full witness data establishes the stronger forward-only statement.

## Branch coverage and termination status

After propagation, the search chooses one nonsingleton domain and recursively visits every value in that domain, using a separate domain-list copy for each child. Every reduction used before branching is sound. A branch is rejected only by propagation; otherwise it reaches a singleton assignment or every child is exhausted. Consequently a normal return with no solution represents exhaustion of the normalized model after the explicitly witnessed exclusions.

A node or time limit raises `TimeoutError`, which propagates out of the recursion and produces status `LIMIT`. It is not converted to an exhausted branch. Time is checked at node entry, rather than inside propagation, so a propagation call can overrun its nominal budget. This can affect timing precision, but it does not turn an incomplete traversal into `EXHAUSTED`: either the traversal actually completes, or the next checked node reports the limit.

The outer `COMPLETE` status means that every requested partition was processed; it does not assert that each individual partition exhausted its search. The recorded individual statuses were therefore inspected, and all 70 are `EXHAUSTED`. The full-run output is separate from the output filename used by the optional single-index mode.

## Exact scope

The reviewed native evidence supports this restricted conclusion: every induced $98$-edge target with the saved source's indexed histories fixed outside any chosen four coordinates belongs to one of the explicitly witnessed isometric assignments after normalization. Undoing normalization preserves cube-isometry class. The scope includes every four-coordinate partition and does not require slice-isometry extendibility.

It does not classify all $98$-edge paths, address changed lengths or index matching, or prove a global bound in $Q_9$. Any statement about the minimum number of changed histories must retain the fixed source, fixed length, indexing, and chosen orientation convention.

No Lean proof of the exclusions is supplied by the result JSON or by this review. A kernel-checked conclusion still requires the geometric model bridge, complete finite search certificates, and verified isometry witnesses, linked to the same explicit source data. The recorded script digest is `d91628352e9652b422495262c4a98d254f55afdc499cee3d53677be25af61ef3`; the input digest is `d62c92cc97eae196b21aeefe2111adfb03cc3121b9b62ba7e3e2c6ee6920c20d`.
