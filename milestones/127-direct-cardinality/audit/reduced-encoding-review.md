# Review of removing the six lower-bound counters

The proposed contradiction transport is sound for the existing pipeline of ordered positive-hint unit-propagation deductions. It does not require a new existential projection theorem. The reduced formula and its identifier map have not been generated or checked by this review; the conclusions below specify the conditions the implementation must satisfy.

This is a separate design review. The frozen prelude audit, its evidence and its source are unchanged. No native search, compiler, proof replay or encoding experiment was run.

## Exact intended reduction

The original formula has 106348 clauses and 7277 variables. The six individual lower bounds on the absent-corner counts are \((1,2,1,3,1,1)\). Each is currently represented by an at-most counter on its 21 selected-corner literals, with cap \(21-k\) for lower bound \(k\).

For 21 literals and cap \(q\), the existing counter allocates \(21q\) variables and emits

\[
q+20(2q+1)=41q+20
\]

clauses. Thus the six lower-bound counters contribute:

| Absent-corner lower bound | Centres | Selected-corner cap | Variables per centre | Clauses per centre |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 4 | 20 | 420 | 840 |
| 2 | 1 | 19 | 399 | 799 |
| 3 | 1 | 18 | 378 | 758 |
| Total | 6 | | 2457 | 4917 |

Removing precisely these 4917 clauses and appending the already proved 235 direct clauses gives

\[
M=106348-4917+235=101666
\]

reduced input clauses. Retaining the variable numbering keeps the declared variable count 7277; the 2457 removed-counter variables become unused. They are not replaced by new variables or compacted identifiers.

The deletion criterion must select all clause families of each of the six lower-bound counters, including initialization, zero-register, propagation, monotonicity and overflow clauses. It must leave the endpoint counter, the joint six-count upper-bound counter, and every geometric clause unchanged. Counter family identity should be checked independently of a numerical clause-range assumption. The prepared result should verify that all 2457 variables occur only in the deleted families and nowhere in the retained formula or direct clauses.

The count calculation follows the inspected counter implementation. It is not a verification of an as-yet-unwritten deletion list.

## Why a reduced contradiction suffices

Every retained input is either an original clause or one of the 235 clauses already derived from original inputs. Therefore every assignment satisfying the original formula also satisfies the reduced formula. If the reduced formula has a checked contradiction, the original formula has a contradiction as well.

This implication is sufficient for an upper-bound proof. Removing original clauses weakens the available premise set, so the proof need not justify their removal. The required justification concerns the appended direct clauses, which the frozen prelude supplies.

For the concrete proof transport, retain the original 106348 inputs and append the frozen prelude at identifiers 106349 through 106583. Each reduced input identifier \(i\), where \(1\le i\le M\), must have an explicit map to the identifier of its identical retained original clause or its identical prelude clause. The input map must preserve clause occurrences and literal order. Equal clause text does not justify silently merging distinct input identifiers.

A native derived identifier \(x>M\) maps to

\[
106583+(x-M)=x+4917.
\]

The first possible derived identifier, \(M+1\), consequently maps to 106584. This separates every transported native deduction from the original input range and the entire prelude range. Gaps in the native sequence are harmless; identifier reuse is not permitted.

For each native deduction, apply the input map or this derived-identifier shift to every proof reference. Leave its signed literals and their order unchanged. If the native proof checks by ordered unit propagation, the transported proof checks by the same assignments: each mapped premise has exactly the same literals as the referenced native premise. Additional original clauses in the combined database do not affect a replay that explicitly uses the listed references.

This argument is an induction over the native deductions after the 235 checked prelude deductions. The base consists of mapped reduced inputs, all already present. At each step, every mapped derived reference must be an earlier checked deduction. The final mapped clause must be empty. Trimming and subsequent export must use 106348 as the number of trusted inputs, not 101666 or 106583, and must retain the dependencies of every used prelude clause.

## Deletion records and proof format

Deletion records remove available clauses; they do not derive new clauses or establish implications. There are two sound options for an ordered positive-hint replay with fresh, non-reused deduction identifiers:

1. Preserve deletion records and map every deleted clause identifier by the same input or derived map. Validate native clause availability and the mapped sequence. The leading event identifier on a deletion record must be handled according to the parser's deletion-record convention; it must not be inserted as a new clause.
2. Omit deletion records from the transported replay and retain all previously checked clauses. Every listed positive reference still denotes a proved clause. Keeping these clauses does not change the unit status of a referenced clause under the assignment generated by the explicit hint sequence.

The second option fits the inspected existing trimming pipeline, which skips deletion lines and rejects negative proof hints. If it is used, the audit should explicitly record this choice. It should still verify that every native referenced identifier was an input or a prior deduction, that no derived identifier is reused, and that every transported deduction independently passes the positive-hint replay. The original native trace and its deletion records should remain preserved as provenance.

This argument must not be extended automatically to general RAT deductions. RAT obligations can depend on all clauses containing a particular pivot polarity. Adding back omitted original clauses, or ignoring deletions, can create extra obligations. The current transport should reject negative or unsupported hint groups unless a separate complete RAT transport and checker is implemented. No such implementation is part of this proposal.

## Existential projection and positive search results

A contradiction needs only the implication from the original formula to the reduced formula. Claiming that the encodings have exactly the same possible selected-vertex configurations requires the converse extension argument as a separate statement.

The expected extension argument is elementary. The direct clauses at a centre assert that at least \(k\) of its 21 corners are absent, equivalently that at most \(21-k\) selected-corner literals are true. Assign each removed counter register to the truth value of the corresponding partial-count threshold. The existing counter clauses are then satisfied. This extension does not change any other variable, provided the removed registers occur nowhere outside their own deleted clauses.

That gives equivalence after existentially quantifying the 2457 removed register variables. It does not give equivalence for arbitrary fixed values of those registers: the reduced formula ignores them, whereas the original formula restricts them. The direct-clause completeness proof and counter interpretation support the extension argument, but this review has neither implemented it for the proposed reduced file nor added a Lean theorem.

If the reduced native search returns a satisfying assignment, the unused-register values printed by the solver should not be assumed to satisfy the original counters. Reconstruct the registers from the selected-corner counts and verify the extended assignment against every original clause. A complete induced snake still requires the usual separate connectivity, endpoint and induced-adjacency checks. A timeout supplies no conclusion.

## Conditions for accepting an implementation

An implementation can be accepted after checking the exact original and prelude hashes, the six removed counter families and their 4917 clause identifiers, the 2457 now-unused variables, and the exact 101666-clause reduced input. Every reduced input must map to an identical justified clause. A terminal negative result must then supply a complete transported contradiction with all positive hints replayed against the original inputs plus the prelude derivations. The native source, reduced input, map, raw trace, transported trace, trimmed trace and their terminal statuses should be preserved separately.

This review does not predict a runtime or proof-size improvement. It establishes a sound route for using a smaller redundant encoding if the implementation and its resulting proof pass those checks.

## Evidence inspected

The frozen prelude audit is `audit/prelude-review.md`, SHA256 `da0425890434e849aa785c7c65b50b5be9e2f38e554c745978cf65f901af9485`. Its JSON evidence is `data/prelude-review.json`, SHA256 `3f5eb4263bc4a33259ba94fa96d6334584c6cafb6f5413c19cd33f4e3f80ed5a`.

The counter allocation and clause families were read from `milestones/10-window-aggregate/scripts/gen_lean_sat.py`, whose preparation pin is `33e6094ba48ddd8fa6cb7c9e9c2c2cab15c4e9a68908b0427125a2b11c683ecd`. The prior bounded-search source and the proposal record specify the original six lower bounds and preserve variable identities. The existing trimming parser in `milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py` skips deletion lines and requires positive hints. No source file was changed by this follow-up except this new review.
