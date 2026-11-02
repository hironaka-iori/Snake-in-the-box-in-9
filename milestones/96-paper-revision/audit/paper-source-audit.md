# Revision 96 source audit

Audit date: 3 November 2026. Scope: manuscript revision 86 and milestone evidence 87–95. This audit is read-only outside this new note. No compiler, solver, replay, external service or other thread was used.

Both inspected manuscript copies have SHA-256 `eb9d5581336060b799e93b7532f59cdb485ce7f5ee39b28bd2f0fdfba4a09ec3`:

- `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`
- `E:/Snake-in-a-box/paper/snake9_research.tex`

All manuscript line numbers below refer to those exact bytes. The evidence cited here records successful existing checks; this audit did not rebuild their dependencies.

## Principal conclusions

The global interval remains $191\le a(9)\le235$. The proposed upper bound 234 still depends on five unfinished count-independent share targets, the remaining weight interpretation, full graph coverage and the complete potential check. The archived contributor proof of 235 is independent of completing this newer charge-model argument.

Three additions are mathematically substantive:

1. A graph defined directly from accepted full transition keys has a checked conditional arbitrary-snake coverage theorem. Its exact endpoint formulas are part of its definition. Full finite coverage and the two reference-catalogue premises remain assumptions.
2. Every compatible eleven-direction word for each of the 55 history share signatures is classified exactly: 69 words, with 41 singleton and 14 doubleton classes. All 69 geometric bounds and eight stronger capped bounds have now been supplied. The final history-credit theorem has only the snake and fitting-window hypotheses; no per-word bound remains assumed.
3. For three fixed saved weighted graphs, cycle and short-path certificates jointly constrain slope and global potential range. They prove optimality of the reported rational comparison values among all admissible rational slope/range choices. This is stronger than proving the minimum cycle mean for a fixed slope.

## Dependency-ordered revision

### 1. Preserve the established foundations

Keep the existing main theorem, square census, endpoint arguments, integer-share budget, local inequalities, sharp complete-path witnesses, boundary contribution 21, and conditional potential criterion. Preserve all author and hyperlink metadata byte for byte. Keep the historical finite-model results and cycles with their stated scope. No evidence in 87–95 changes their constants or proves a new global bound.

The authors are Iori Hironaka, Tommy Ma, Steven Zhan. The existing PDF author string is `広中依緒璃, Tommy Ma, Steven Zhan`; do not replace it while revising prose.

### 2. Complete the history interpretation after exact recognition

Suggested placement: after the overlap-signature notation in `sec:state-filter-bridge`, or split into a short classification subsection after `sec:exact-history` and a credit proposition immediately after the filter results. Reuse $\operatorname{can}$, $\mathcal S(w)$, $b_j$, $\alpha_j$, and $\sigma_{12}$ rather than introducing another collection of terminology.

Suggested classification statement:

> For each of the 55 saved share signatures, the listed canonical eleven-direction words are exactly the induced eleven-direction words in nine coordinates whose three overlapping canonical nine-direction windows have that signature. The signatures are distinct. Forty-one have one compatible word and fourteen have two, giving 69 words in total. Whenever a fitting transition at index $r$ emits one of these signatures, $r\ge2$ and $\operatorname{can}(d_{r-2},\ldots,d_{r+8})$ belongs to its listed set.

Proof structure: canonicality fixes the first nine letters; the remaining two letters have only $9^2=81$ choices. Check canonicality, inducedness and all three window equalities for each choice. Complete finite coverage gives one inclusion; direct validity of every listed word gives the other. Exact history recognition identifies the three actual windows and excludes emission at $r=0,1$. This proves local compatibility, with no assertion that each listed word extends to a long snake.

Suggested completed history-credit statement:

> Let $x_0,\ldots,x_m$ be a snake and let $r+9\le m$. Consider all geometric credits attached to history signatures emitted at $r$, together with each stronger capped credit whose count tests hold. Then
> \[
> \max\bigl(\{0\}\cup\{\text{these applicable credits}\}\bigr)
> \le\sum_{i=4}^{8}\sigma_{12}(x_{r+i}).
> \]
> This statement holds for the complete saved list of 55 history share rules.

Proof structure: every emitted signature selects one of its complete compatible-word list. The corresponding geometric inequality is supplied for every word. The eleven-direction window begins at $s=r-2$, so offsets $6,\ldots,10$ become $r+4,\ldots,r+8$. A cap at stored six-count position $k$ concerns $\alpha_{r+k+3}=\alpha_{s+k+5}$, where $0\le k<6$. Every stored cap is strictly below six, so $b_{r+k+3}\le c<6$ implies $\alpha_{r+k+3}\le c$. The eight stronger capped bounds therefore have the same conclusion. One uncapped credit is transported from the nine-direction suffix, whose centres agree. Each candidate bounds the same sum, so their maximum does as well.

The concrete result needs no reference-catalogue premise, graph-cover premise, or pending count-independent share target. Those belong to later global assembly. The finite maximum is valid even if multiple rules apply. Adding these alternatives would require another argument.

Evidence:

- `94-history-share-dispatch/lean/HistoryShareValidity.lean:43`, `saved_variant_iff_fits`: exact characterization.
- `94-history-share-dispatch/lean/HistoryShareCounts.lean:5–18`: distinct signatures and exact 69/41/14 counts.
- `94-history-share-dispatch/lean/HistoryShareAssembly.lean` and successful `data/HistoryShareAssembly-audit.json`: all-rule coverage and actual emitted-word membership.
- `94-history-share-dispatch/lean/HistoryShareCaps.lean` and successful `data/HistoryShareCaps-audit.json`: strict-cap transport and common centre positions.
- `95-history-credit-integration/lean/HistoryCreditEvaluator95.lean:25–95`: all rule obligations, contribution and maximum arguments.
- `95-history-credit-integration/lean/ConcreteRules95.lean:96–100`: final concrete theorem; hypotheses exactly a snake, index $r$, and $r+9\le m$.
- `95-history-credit-integration/data/ConcreteRules95-audit.json`: exit 0, `PASS_COMPATIBLE_CREDIT_MODULE`; source SHA-256 `55e1aa1d2b5ba88639f5cf09ba274e47375452566fb06655e36859eb207ff9a0`; final theorem uses standard axioms only.
- `95-history-credit-integration/data/proof-summary.json` and `data/checkpoint.json`: complete closure, literal model comparison and 923 audited theorem declarations. The latter number includes auxiliaries and additional preserved instances; it is not a count of distinct new share bounds.

### 3. State graph coverage with its exact remaining hypotheses

Suggested placement: after `prop:reference-union-retention`, replacing the current paragraph at lines 1479–1493 which insists on external-array identity.

Define the graph by all full keys accepted by its finite acceptance tests. A key consists of the nine-direction identifier, current history identifier and six-count word. Its source and target are determined by the existing direction/history update and five-count shift. Keep parallel edges distinguished by their full keys, since endpoint equality does not determine a weight.

Suggested conditional statement:

> Assume both reference-catalogue refutation premises and that, for every assigned context, its acceptance test includes every count word retained by the stated local filters. Then every snake determines a walk in the graph defined by those accepted keys. For $m\ge8$ it has $m-8$ transitions, and its transition at $r$ is the actual direction/history key with count word $(b_{r+3},\ldots,b_{r+8})$.

Proof structure: the state-sequence theorem supplies the source and target states. Local retention and the two reference premises show that the actual key passes the retained predicate. Coverage puts this key in the defined graph; its endpoint formulas give the successive actual states. The finite assignment of contexts is already checked; the complete family of individual acceptance-coverage certificates remains unfinished.

The existing generic endpoint-only walk theorem omits full-key equality from its conclusion. For weight interpretation, retain the stronger exact-key witness available from the assembly argument, or apply the key-indexed edge inequality directly. A manuscript proof should say explicitly that the selected edge is the actual full key.

Defining the graph this way avoids an external-array identity obligation only when the subsequent weights and potential inequalities are checked on the same defined graph. The acceptance tests may conservatively admit extra keys. Every admitted key must satisfy the potential inequality, including any extra keys. Equality of old and new edge counts or common endpoints is insufficient.

Evidence:

- `87-retained-array-membership/README.md`: one-sided coverage is sufficient; 206,589 endpoint pairs have two rows, so parallel full keys matter.
- `88-retention-diagram-certificate/README.md`, `89-shared-cover-certification/README.md`, `90-context-witness-certificates/README.md`: generic acceptance, shared finite covers and context-dependent witness heads.
- `91-reference-shape-reuse/README.md`: proof reuse experiment; no new mathematical hypothesis is discharged there.
- `92-full-witness-batch/lean/DefinedProofGraph.lean:22–53`: coverage and actual-walk theorems retain the full class-coverage family, assignment equality, and two reference premises; endpoint columns are defined directly.
- `92-full-witness-batch/data/DefinedProofGraph-audit.json`: successful three-theorem receipt.
- `92-full-witness-batch/README.md`: context assignment complete across all 37,875 direction/history contexts; full coverage family remains pending.
- `93-defined-graph-potential/audit/weight-bridge-plan.md`: exact full-key weight dependencies and endpoint-only interface limitation.

Do not quote a frozen partial class count as a current live result. Milestone95 records 86/127 witness classes and 89/127 geometry classes at its checkpoint. A newer completed family claim requires its successful final assembly receipt.

### 4. Add the joint slope/range comparison result

Suggested placement: after the completed/conditional graph table and before `sec:short-walk`. Keep the existing short-walk obstruction for weakened catalogues, which addresses a different set of graphs.

Suggested general proposition:

> Fix a weighted directed graph. Suppose it has a cycle of mean $M$ and a walk of $k$ edges and weight $C$. Let a potential with slope $M$ have global range at most $R$, where $R=kM-C$, and put
> \[
> B_* = \frac{1098960+8M+R}{4200+M}.
> \]
> Assume $4200+M>0$ and $k+8\le B_*$. Then every rational slope $\mu$ and potential of global range at most $\rho$ satisfying
> \[
> \mu+\pi(v)\le w(u,v)+\pi(u)
> \]
> on every edge, with $4200+\mu>0$, obeys
> \[
> \frac{1098960+8\mu+\rho}{4200+\mu}\ge B_*.
> \]

Proof: summing around the cycle gives $\mu\le M$. Summing along the specified open walk and using the global range gives $k\mu-C\le\rho$. Consequently

\[
\begin{aligned}
1098960+8\mu+\rho-B_*(4200+\mu)
&\ge1098960-C+(k+8)\mu-B_*(4200+\mu)\\
&=(k+8-B_*)(\mu-M)\ge0.
\end{aligned}
\]

The identity uses $R=kM-C$ and the definition of $B_*$. Division by the positive competing denominator proves the result. A feasible baseline potential makes this a joint optimum, rather than merely a lower obstruction on comparison values.

Exact application table:

| Fixed weights | $M$ | $k$ | $C$ | $R$ | $B_*$ |
| --- | ---: | ---: | ---: | ---: | ---: |
| Completed local floors | $483$ | 9 | 3796 | 551 | $157625/669$ |
| Additional proposed $012034$ floor 20 | $9259/19$ | 31 | 14512 | $11301/19$ | $20965613/89059$ |
| All nine target floors | 496 | 7 | 2872 | 600 | $137941/587$ |

The attaining cycles have lengths and total weights $(4,1932)$, $(19,9259)$ and $(3,1488)$. All three satisfy $k+8\le B_*$. The integer comparisons are 235, 235 and 234 respectively.

Scope: the baseline potentials, cycles and paths were independently checked against all saved edge arrays or their relevant saved entries. The algebraic comparison theorems have Lean receipts. Their concrete graph membership and complete feasible potential have not all been embedded in the defined-graph Lean environment. The fixed-graph conclusion therefore concerns the specified saved weighted graphs; it is not a new arbitrary-snake bound. The completed profile cannot reach 234 by changing only its constant slope and global potential range. Improvements need changed weights, admitted transitions, endpoint-dependent bounds or a different charge budget.

Evidence:

- `93-defined-graph-potential/lean/PotentialComparison.lean`: seven telescope, deficit, slope and rational comparison theorems.
- `93-defined-graph-potential/data/PotentialComparison-audit.json`: exit 0 and all seven standard-axiom audits.
- `93-defined-graph-potential/data/*-range-certificate.json`: exact cycles, open walks and potential ranges.
- `93-defined-graph-potential/data/range-certificate-review.json` and `audit/range-certificate-review.md`: independent integer recheck, 73 witness occurrences / 61 distinct full keys, and accepted-key checks.

### 5. Replace the closure list with the residual dependencies

Preserve the local-target list, while separating these remaining tasks:

1. Complete the five pending count-independent share targets required by the full profile.
2. Supply the complete acceptance-coverage family and discharge the two reference-catalogue premises in the common checking environment.
3. Combine all weight components on the actual full key. The history component is complete. The other components and their literal correspondence to the chosen weight profile require their own common-environment assembly.
4. Check every edge inequality and the potential range for the graph defined by the accepted keys, then apply the existing boundary and open-walk budget.

For the completed-floor profile, the five stronger target premises are unnecessary; its currently certified finite-array comparison only yields 235. For the full profile, mean 496 and range 600 still give strict margin 32 at length 235, conditional on the remaining dependencies.

## Stale text and corrections

- Abstract, line39; overview/evidence table around85–97: add completed history interpretation and joint potential optimality. Retain the global interval and five pending targets.
- Line1070 and `sec:verification` lines1968–1970: the claim that $012034$ contradiction replay is ongoing is stale. The saved attempt stopped at Check1 timeout; the target remains pending. Paper prose can simply state that no completed contradiction replay and final audit are available.
- Line1263: replace the blanket statement that every credited share lacks interpretation. The complete history component is proved; whole-weight assembly is still pending.
- Line1295: replace the prospective coverage requirement with the exact 55/69 classification. Preserve the explanation of why ambiguity requires all compatible words. Distinguish taking the minimum across a signature's compatible realizations from the maximum across alternative valid credits for one actual share sum.
- Lines1479–1493: replace mandatory retained-array identity by conditional coverage of the graph defined directly from accepted full keys. Preserve the two reference premises.
- Lines1499–1540: retain all four existing table rows and the one-floor comparison; add the joint optimality proposition and the three exact path certificates.
- `sec:closure`, lines1720–1738: remove history credit as an unfinished task; update graph coverage and potential scope.
- `sec:verification`, lines1973–1990: update completed history semantics and conditional defined-graph coverage; retain explicit checking boundaries for saved-array minima and complete global deductions.
- Bibliography around3978–3995: add a pinned source covering87–95 and cite it at the new propositions. Keep older sources attached to the results they establish.
- Several source comments in93–95 say “awaits compilation” despite successful later receipts. Cite the receipts and final checkpoints rather than copying those comments. The older93 weight-interface audit's largest unresolved history component was resolved in94–95.

## Mathematical cautions

- Keep edge length $m$ separate from vertex count $m+1$ and from the $m-8$ graph transitions. State $m\ge8$ before subtraction in prose; shorter paths are already below all bounds discussed here.
- Use scale-12 shares exactly once. Saved credits already have those units; the graph weight is $120b_{r+8}+L$, with no additional factor12 on $L$.
- The saturated symbol six denotes an interval $[6,21]$. Only caps strictly below six transfer directly to actual upper bounds. Current history caps are1,2,5.
- Distinct full keys can have equal endpoints and unequal applicable credits. Avoid defining the weight as a function of endpoint pairs alone unless parallel-edge information is retained.
- One-sided accepted-key coverage suffices for snake membership, but it does not transfer a potential checked only on an older row array to conservative extra edges.
- The exact 69-word classification is local. It does not certify extendability of every configuration to a long snake or coexistence of independently chosen configurations.
- The concrete history theorem is fully discharged at the stated local level. The global234 conclusion is still conditional.

No additional mathematical error was found in the inspected established inequalities. The main issues are outdated proof-status descriptions, an unnecessarily restrictive external-array route, and missing integration of the new exact classification, completed history credit and joint comparison theorem.
