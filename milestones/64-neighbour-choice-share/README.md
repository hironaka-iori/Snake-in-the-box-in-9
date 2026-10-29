# Milestone 64: complete neighbour-choice share bounds

Thirty-four improved empty-square share bounds on eleven-transition windows have passed Lean for arbitrary matching snake segments. Incorporating them into the existing restricted graph gives exact minimum **1991/480**, compared with **4973/1200** in milestone 63. The increase is **3/800**.

The complete replay and dependency audit passed **36 modules and 216 theorem checks**, including all 34 arbitrary-snake instances, the exhaustive case-coverage theorem and the finite potential with an attaining cycle. The project global interval remains **191 <= a(9) <= 235**. Nothing here establishes the optimum or a stronger global bound.

## Mathematical construction

Let W be an induced segment with eleven transitions, and let C be its final five internal vertices. Each end of W already has one selected neighbour inside W. Its possible additional selected neighbours therefore form a set containing at most one selected vertex. Vertices already forced absent by W are removed from this set of possibilities.

For each end, enumerate the choices of no additional selected vertex or exactly one candidate. For each joint choice:

1. Add the chosen vertices to the known selected set.
2. Declare every unchosen candidate neighbour absent.
3. Force further absences whenever selecting a candidate would produce degree at least three at a selected vertex.
4. Count the empty-square share guaranteed by these absence facts.

Every actual snake belongs to one of the joint choices. The minimum of the branch share bounds is consequently a lower bound for the original window. The two ends used here are the ends of a local segment; no weighted charge based on the global snake endpoints is introduced.

The Lean coverage proof has a slightly more general form. A finite check establishes that any two distinct members of each candidate list cannot both be selected. It then proves that the selected elements of that list are either absent entirely or comprise one listed choice. The branch theorem derives the share inequality from forced absences, and the final theorem transports the result to arbitrary matching snake segments under coordinate permutations and translations.

## Computation and verification

The complete family contains 218 transitions and 214 distinct direction shapes. Independent reconstruction checks **11,554 joint neighbour configurations** and all 4,608 square faces. There are 34 improvements over the inherited weights.

For the improved windows, **2,044 branch certificates** have been reduced to the absence facts needed for the claimed lower bounds. The independent verifier checks that every reduced mask is justified and still reaches the same bound. The compression changes the certificate size, not the inequalities or graph weights.

The checked integer-weight minimum is 1991/4. An exact potential and an attaining cycle verify this finite graph calculation. The potential range is 2417. Even with zero range loss, the eleven-transition threshold for 234 remains higher by

\[
\frac{112440}{225}-\frac{1991}{4}=\frac{119}{60}.
\]

The new attaining cycle differs from the pilot cycle in milestone 63. That pilot gained 19 units in total; evaluating the full family gives a smaller increase in the minimum. This reinforces the need to test every critical-family transition and recompute the minimum.

Verification receipts:

- `data/verification.json`: successful independent reconstruction, including the compressed masks and exact finite potential.
- `data/partial-lean-audit.json`: a historical snapshot from the running replay; superseded by the complete audit.
- `logs/build-record.json`: source hashes, completion codes and output locations for the current replay.
- `logs/controller.log` and `logs/replay-two-workers.log`: completed replay logs after reducing concurrency to two workers.
- `data/lean-audit.json`: the successful complete audit of all 36 modules and 216 theorem-dependency checks.

The initial combined check was stopped because of its memory cost. The checks were separated by branch and their masks reduced. One complete compressed local instance then passed in 225 seconds. The first three-worker batch was reduced to two workers to limit memory use; its completed modules are preserved by source-hash-aware resumption. These resource interruptions are not mathematical refutations.

## Exploratory next steps

Two pilots were run without changing the claimed graph weights:

- Applying the recorded six count constraints after each neighbour choice gives candidate share improvements on four windows of the new attaining cycle and candidate contradictions on three others. All count deductions remain outside the Lean-checked package and require a count-to-geometry bridge and replay of their deductions.
- Rejecting a branch whose known selected vertices already form a complete cycle improves only one transition, outside the current attaining cycle. This gives no improvement on that cycle and is currently a lower-priority extension.

The count-conditioned route is therefore the stronger next test. It should be assessed on the complete family, with share improvements kept distinct from candidate validity exclusions.

## Next step and manuscript schedule

The next task is to prove the count-conditioned deductions, beginning with the saturation rule that converts a tight absence-count bound into further selected vertices. The preliminary gains and contradictions remain excluded from this milestone's checked graph. Full graph-to-snake assembly and inherited numerical premises remain unresolved; these local and restricted-graph results do not establish a new global upper bound.

This completes research round **8 of 10** after manuscript revision 56. The next full manuscript rewrite remains scheduled for milestone 66. The repository paper and existing editor mirror remain unchanged and synchronized. The compiler limitation recorded at milestone 56 remains unresolved.
