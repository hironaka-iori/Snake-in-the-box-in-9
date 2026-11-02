# Independent manuscript review

Reviewed the complete 4,302-line pre-revision manuscript, including every appendix, printed catalogue, witness sequence and bibliography entry. The stable original is `data/paper-before.zip`, member `snake9_research.tex`, SHA256 `7d4d974bc353ca723e4a5362b0960610d959dfe622b115b629968818c178875c`. Subsequently reviewed the complete revision diff and the revised graph, weight, potential, closure and verification sections.

Final reviewed manuscript SHA256: `f649b4dfc0b3f11958105517d00f567db591517e5a3434e1dfad3cfc212b3429`. This report makes no manuscript changes and records no new compilation, numerical search, or universal upper bound.

## Conclusion

The revised main argument states the present dependency chain accurately. Complete finite coverage, preservation of the actual full edge key, all weight components, the total charge budget and the conditional potential implication are established by the cited checked developments. The exact 1,378-key reference refutation and complete graph-potential certificates remain explicit assumptions. The proposed bound 234 additionally needs the five local share bounds.

No critical mathematical error was identified in the revised chain. The distinctions between the older floor-20 profile with range 600 and the current floor-18 profile with sufficient range 602 are maintained. The older tight path proves no range-optimality statement for the latter profile.

## Main findings and disposition

Line references marked “original” refer to the archived source; current references refer to the final reviewed hash. Labels are the stable references.

1. **Obsolete finite-coverage assumptions, corrected.** Original lines 1264, 1578–1619, 1927–1936 and 2183–2189 still left all-class coverage and key-dependent weight interpretation open. Current `prop:defined-graph-walk`, lines 1575–1605, correctly uses the completed 127-class coverage and context assignment, preserves the complete direction/history/count key and both endpoints, and assumes only the exact reference-union refutation at this step. The older milestone92 summary is a partial checkpoint; its later successful `CloseBatch` receipt and milestone97 observations supersede that checkpoint for coverage.

2. **Reference assumptions, corrected.** Original `prop:reference-union-retention` required both complete contributor catalogue propositions. Current lines 1440–1474 use the exact 1,378 selected keys directly, matching the five implications checked in milestone105. This does not establish any of their refutations. Selection of source entries, validity of table keys and absence of unused roots must remain distinct from contradiction certificates. The revised text makes this distinction.

3. **Actual weights and boundary budget, corrected.** Current `thm:actual-weight-budget` identifies the nine-direction geometric, history, four earlier count-conditioned, share-120 and count-free alternatives on the same five centres. Combining them by their maximum is valid; adding them would be invalid. The indices $r+4,\ldots,r+8$, entering count $b_{r+8}$, $m-8$ edges and omitted singleton positions $0,\ldots,7,m$ agree with the checked actual-snake statements. The reference hypothesis is unnecessary for the weight budget itself. The displayed deduction
   $$
   W+2520\le 5G_{12},\qquad W+4200m\le1098960
   $$
   has the correct constants.

4. **Conditional local premises, clarified during review.** The first draft of `cor:reference-potential-bounds` introduced the general potential consequence before explicitly assuming the selected conditional floors. Current lines 1677–1680 now state those five local-share premises first. Thus both substitutions are supported:
   $$
   4683m\le1103375,\qquad4696m\le1103530.
   $$
   These give 235 and 234, respectively, when the stated reference and entire-graph potential hypotheses hold. Partial context certificates cannot replace the entire-graph premise.

5. **Floor reduction, retained with correct limits.** Original comparison lines 1632–1652 concern floor20/range600 and strict margin32. The revised table and `sec:least-floors` separately state floor18/range602 and margin30. The five listed obstruction deficits are arithmetically correct: $632,633,632,632,632$, with all path lengths at most227. Monotonicity of the maximum credit proves the claimed integer-box classification from those certificates. The result concerns the fixed graph, fixed other credits and boundary formula; it proves no universal local share minimum. The manuscript explicitly retains this limitation and the independent computational status of the concrete certificates.

6. **Abstract attribution, corrected during review.** Current line39 now attributes $39m+2s_0\le9200$ to both the square census and the six-centre count estimate. The census alone gives the earlier identity involving $T$ and cannot supply coefficient39 without the count bound.

7. **Archival 235 versus current proof environment, retained.** The abstract, `sec:upper-proof` and `sec:verification` continue to attribute the existing 235 theorem to the archived contributor development and disclose the pending independent rebuild. The new reference-union interface does not supply that rebuild. No new unconditional bound is claimed.

## Definitions and terminology

The remaining definitions serve repeated mathematical use: induced paths, singleton counts, truncated counts, integer shares, canonical words, actual states and the edge weight. Removing the separate definition environments for endpoint blocking and the zero-bonus subgraph is appropriate; their ordinary prose descriptions remain sufficient. The critical-cycle notation is standard and repeatedly used in the subsequent criterion.

The sentence “No additional symbol for this assumption is needed” was editorial commentary rather than mathematical content and has been removed. No further new definitions are needed for this revision. Keep implementation names, receipt counts and traversal details in the research record rather than introducing additional manuscript terminology. The full edge key remains necessary because parallel edges can have different weights.

## Appendix disposition

**Preserve the appendices verbatim in this revision.** Their complete contents were read, including the historical graph models, radius-four and radius-three proofs, detailed geometric classifications, all175 forbidden pairs, construction experiments, diagnostics, transition sequences, blockers, return witnesses, finite checking procedure and all55 history-share rows.

The region from `\appendix` through the `\clearpage` preceding the bibliography is byte-identical between the original and final reviewed source: 183,560 bytes, SHA256 `4225b0b97881fdfdb92f69d0e69505d1c38de22dfabb0a8714b635de270928f1`. Their earlier incomplete calculations are explicitly historical, restricted or conditional. Their older state counts and potential ranges should not be replaced by present-model values.

Two minor pre-existing editorial points can be addressed separately if those appendices are later revised:

- Original line3144, opening `app:bound238`, refers to the radius-four bound “in the main text”; its detailed presentation is now `app:bound236`. An explicit appendix cross-reference would be clearer.
- Original `prop:window-aggregate` proof, lines3083–3090, begins with two- and three-position potential states. The short paths lacking those internal positions satisfy the stated upper bounds immediately, but that trivial case split could be stated explicitly.

Neither point changes an estimate, witness, catalogue entry or the new proof chain. No appendix proof was recompiled and the printed witnesses were not independently rerun by this review. The geometric classification is correctly labelled a proof outline where individual branches are omitted.

## Evidence and verification limits

Read the milestone97–99 and105 proof summaries, successful milestone92 `CloseBatch` receipt, milestone97 full coverage observation, milestone97 floor-sensitivity and floor18 verification reports, milestone98 weight-model audit, and the live milestone104 progress record without modifying it.

Key receipts:

| Evidence | SHA256 |
| --- | --- |
|92 `CloseBatch-audit.json`|`00b9388a74af98201a0fce6ed52ef5f5a38b89005371b78f0c24cde9136b8dce`|
|97 `proof-summary.json`|`cb54bd5757caa66dc0cab2b55c20cc58b1f1838e95dc9f5bdd8baeff45806e9e`|
|98 `proof-summary.json`|`555fb072822119036363ca2abc811c775c90885627a29b83dcbd9b7add241676`|
|99 `proof-summary.json`|`4068c2429b9bccc51ff23e76523ba34112abf44e942c9296202c071fd67415d0`|
|105 `proof-summary.json`|`2c0b88cea651b5f35750854e6c05d9e7712770682075928a80cd00d06cd18a9f`|

The observed milestone104 record remained RUNNING and explicitly marked complete graph potential certificates false; the manuscript correctly states partial coverage without embedding a volatile progress count. The inspection checks the mathematical implications and their stated receipt scope. It is not a fresh replay of the full dependency closure, an external literature verification, a TeX compilation, or a rendered-page inspection.
