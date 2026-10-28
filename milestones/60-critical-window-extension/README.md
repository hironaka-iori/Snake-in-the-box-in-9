# Milestone 60: extending the recorded critical cycle

This round continues the empty-square route by testing longer versions of the twenty-step cycle that attains the minimum in milestone 59. It establishes two limits of that particular obstruction: its ten-transition empty-square charge remains too small, and three proposed eleven-transition windows violate the induced-path condition. No improved global upper bound is established. The contributor-checked interval remains **191 <= a(9) <= 235**.

## Complete ten-transition probe of the saved cycle

Every adjacent pair of nine-transition words in the recorded cycle has exactly one compatible induced ten-transition extension, up to coordinate relabelling. The enumeration tests all nine possible actual coordinates, then identifies equivalent choices of an unused coordinate. It also checks the overlap of the six stored count symbols.

For each extension, the first nine internal vertices force their off-path neighbours to be absent. The last five internal vertices receive the geometric corner-share charge. Ten of the twenty windows have a positive bound; their total geometric credit is 72. Combining these bounds with the inherited bounds by taking the maximum gives total integer weight 9912, hence mean

\[
\mu=\frac{9912}{20}=\frac{2478}{5},
\qquad \frac{\mu}{120}=\frac{413}{100}.
\]

This is the mean on the complete extension of this one saved cycle. It is not the minimum of a complete ten-transition model, which has not been constructed.

Ten-transition windows omit nine starting positions. The omitted singleton contribution is at least sixteen: eight internal contributions of at least one and two endpoint contributions of at least four. With the existing fivefold share accounting, the conditional bound would have the form

\[
m\le\frac{1099560+9\mu+\rho}{4200+\mu},
\]

where rho is the potential range divided by its denominator. Even with rho=0, excluding m=235 requires

\[
\mu>\frac{56280}{113}>\frac{2478}{5}.
\]

Thus enlarging the full model to ten transitions, with these credits and this boundary accounting, cannot by itself reach 234 while this recorded cycle remains admitted. Lean checks all twenty geometric inequalities, including the ten zero cases, for arbitrary matching snake segments. It also checks the cycle-weight sum and the conditional arithmetic obstruction.

## Validity controls before further empty-square calculations

At eleven transitions, the same extension procedure stops being a unique cycle extension. One phase has two valid extensions, and three phases have none. At each of the three missing phases, the sole direction-compatible candidate has twelve distinct vertices with an additional edge between its first and last vertices. All twelve vertices form a cycle, so they cannot all belong to a snake.

The three forbidden direction words are listed below; distinct numerals stand for distinct coordinate labels.

| Phase | Direction word |
|---|---|
| 14 | (0,1,2,3,1,0,4,1,3,2,1) |
| 15 | (0,1,2,0,3,4,0,2,1,0,4) |
| 16 | (0,1,2,3,4,2,1,0,2,4,3) |

For each word, Lean checks the canonical vertices, verifies that every vertex has two neighbours in the selected set, and proves exclusion from every matching snake by acyclicity. These are elementary validity controls for the proposed longer windows. The association between those words and the saved cycle is checked by a separate exhaustive enumeration; a Lean theorem about the complete enlarged graph is not claimed.

This result prevents treating the saved cycle as evidence that an actual snake can continue with these directions indefinitely. Other cycles may replace it when longer-window constraints are imposed. The eighteen valid eleven-transition candidates have computed geometric data, but their numerical share values are not added to a complete model or claimed as individually Lean-checked instances in this round.

## Reusable proof for arbitrary window length

The geometric transport theorem now accepts a canonical segment of any positive length and any block of five centres lying within it. It constructs the local snake conditions without imposing singleton-count restrictions, proves forced absence from selected degrees, and transfers the binary-mask share calculation to the original snake under arbitrary coordinate permutations and translations.

This removes the need to rewrite the same transport proof for every longer segment. The finite mask condition states that every excluded mask vertex belongs to the forced-absence set. The resulting proof uses the same monotonicity argument as milestones 58 and 59.

The budget arithmetic is also written for a general window length n. If the omitted singleton contribution is at least n+6, the existing global identity gives

\[
W+4200m\le1100760-120n.
\]

Combining it with a potential inequality over m-(n-1) windows gives

\[
(p+4200d)m
\le(1100760-120n)d+(n-1)p+R.
\]

These are conditional accounting theorems. The necessary graph coverage, exclusion premises and local certificates still have to be supplied for any proposed global application.

## Verification and next step

The completed Lean build has five modules and 137 dependency audits, with no admitted proofs. It covers the arbitrary-length transport, twenty ten-transition share instances, three eleven-transition validity controls and the stated arithmetic. The separate verifier enumerates all 4,608 cube faces, reconstructs every forced-absence calculation, checks all coordinate-extension choices and confirms the three endpoint chords.

The next research target is the complete low-mean family, seeking admissible eleven-transition contexts with stronger forced-empty-square charges. This avoids spending a full-model computation on the ten-transition enlargement already limited by the checked cycle. The work remains on the empty-square route; the cycle controls are used to ensure that the segments being charged can belong to snakes.

Files:

- `scripts/probe.py`: complete ten-transition extensions of the saved cycle.
- `scripts/deepen.py`: eleven-transition validity and branching probe.
- `scripts/prepare_lean.py`, `replay.py --resume`, `audit_lean.py`: geometric and arithmetic proofs.
- `scripts/verify.py`: separate exhaustive checks.
- `data/verification.json`, `data/lean-audit.json`: verification receipts and scope.

This is research round 4 of 10 after manuscript revision 56. The paper and its editor mirror remain unchanged and synchronized. The next scheduled full revision is milestone 66. The compilation limitation recorded in milestone 56 remains unresolved.
