# Logical review of the current certificate route

This note explains the proof decomposition used in round 186. The acceptance status of each concrete statement is recorded separately in data/completion.json. It introduces no stronger numerical bound.

The endpoint counter is sound because its 286 flags refer to distinct cube vertices. A true flag denotes a selected endpoint, and a nontrivial path has exactly two endpoints. A subset of distinct endpoint flags therefore contains at most two true flags. If a physical endpoint were represented twice in this counter, the global endpoint budget would not justify the same literal-count bound. The ordered vertex-list proof discharges precisely this distinctness requirement.

For lists A and B of vertex labels, strict increasing order on A ++ B follows from increasing order on A, increasing order on B, and every member of A being smaller than every member of B. The accepted Boolean append lemma states the corresponding equality of checks. The eighteen small ordering proofs therefore imply the original single counter condition without weakening it.

The share caps use a different count. There are 35 centre-corner occurrences; one physical corner can occur for more than one centre. The contribution at each occurrence belongs to the five-centre sum. Reordering occurrences is valid, whereas deleting duplicate occurrences would change that sum. The threshold-list permutation proof retains all occurrences and all multiplicities.

For a nonnegative integer contribution s, exactly min(s,15) of the thresholds 1 through 15 hold. Hence the number of true threshold occurrences is at most the physical five-centre share sum. If that sum is at most fourteen, the fifteenth output of the totalizer must be false under the intended counting interpretation. Internal counter implications follow from adding lower bounds on the two child counts. The streamed input places each fifteenth threshold after the first fourteen layers; a permutation groups the fifteen thresholds for each occurrence. This supplies the same counting argument for that exact input order.

The structural proofs alone do not prove the input formula unsatisfiable. They support the implication from the stated local model to a satisfying assignment of all input clauses. The concrete clause checks and their composition must establish that implication. A separate complete Lean replay of the 52,489-deduction refutation is then needed to derive a contradiction. Finally, actual snakes must be shown to satisfy every local geometric assumption used by that interpretation.

The local interface was inspected directly in round 147's LocalWindowModel.lean and LocalWindowShareModel.lean. It requires the selected window, selected vertices below 512, selected degree between one and two, absence of a selected subgraph of minimum degree two, identification of selected degree-one vertices as endpoints, at most two distinct endpoints, and the specified singleton-count intervals. AxiomsS adds only the share cap. For this critical input the five count intervals are all [0,21]. A complete geometric transfer must provide these conditions and identify shareSum with the physical five-centre share. Finishing the Boolean contradiction does not itself supply that transfer.

Even a completed critical floor-fifteen theorem would leave the other three local share floors and inherited count/reference/context/graph obligations. Under all of those premises, the established comparison is

\[
(4200+\mu)m+5L\le1098600+8\mu+R,
\qquad \mu=\frac{4454}{9},\quad R=\frac{5421}{9}.
\]

Multiplication by nine gives 42254m + 45L <= 9928453. Since 235 * 42254 = 9929690, nonnegative L excludes m >= 235 by a margin of 1237 in the integer inequality. Thus the conditional conclusion is 234. No additional positive-loss estimate is needed for this profile. This arithmetic does not discharge any of its local or graph premises.

The result proved this round concerns the verification of those premises. The exact maximum, the conjectured value 196 and an unconditional improvement remain unresolved.
