# Tight partner-subset capacity

TightPartner214.lean imports PartnerSubset212 and reuses the existing exception budget and Capacity209 list-capacity results. It contains two exported deductions with two axiom-report commands. No compiler or software tests were run.

The first theorem assumes distinct assigned words within C, O and J; J is contained in O; all chosen and outside values belong to the same finite pool; and N contains every chosen variable that actually shares with a member of J. It assumes
\[
|J|=|N|+\bigl(|\mathrm{pool}|-|C|\bigr).
\]
The separate distinctness premise for J is necessary because list membership inclusion alone would permit repeated identifiers in J.

Let E be the actual outside exception list, whose values are absent from the chosen words. The accepted exception budget bounds its length by the spare capacity. Every value of J occurs in the concatenation of N's values and E's values. Distinct-list capacity, together with the displayed equality, forces this concatenation to have exactly the same length as J. The accepted saturation theorem then says that every value in N and every actual exception value occurs in J.

If x belongs to O but not J, distinctness of O's assigned values prevents its value from occurring in J. Therefore its value belongs neither to N's values nor to E's values. It is not an exception, so it shares with some c in C; that c cannot belong to N. This is the first exported conclusion.

The statement remains valid when N overestimates the chosen partners, so N contained in C is not required by the proof. The intended application uses a duplicate-free candidate list N contained in C. A duplicate-free pool gives its set cardinality; the theorem itself uses list lengths throughout.

The second theorem supplies the actual-sharing premise using current domains: partner lists contain every actual chosen/outside sharer, N contains every listed partner of a J member with intersecting current domains, and the same complete assignment fits all domains. Its support list for x must contain every domain word of every listed chosen partner outside N. The first theorem then places x's actual value in that support list. Intersecting x's domain with support preserves the same complete assignment at every variable.

Partner-domain support may be an overestimate. The proof does not infer that every supported word admits a compatible full assignment. Geometric distinctness, alphabet membership, concrete candidate-list construction and native domain-mask correctness remain separate inputs. No native propagation or traversal, novelty, or global snake bound is claimed.

The source introduces no new global definitions, admitted proofs, axioms, or native_decide. Compilation remains pending with the parent task.
