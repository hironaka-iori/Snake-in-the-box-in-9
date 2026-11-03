# Complete source review for revision 146

Reviewed source: `paper/snake9_research.tex`, 450,526 bytes, 6,126 lines, SHA-256 `c265a8cfd81812ae372e8568a7d45e898ba3e5d08affcbec911b0581d901f696`.

The review read the complete source, including the preamble, all statements and proofs, numerical tables, all witness sequences, the 175-entry exclusion catalogue, the 55-row history-share catalogue and all 63 bibliography entries. The preceding milestone's `MATHEMATICAL_NOTE.md`, `data/verification.json` and `data/checkpoint.json` were read first. Line references below refer to this source hash. No paper, proof source, certificate or root-owned file was edited. No Lean run, solver run, full-graph check, external retrieval, compilation or visual PDF review was performed. Source inspection is not a new proof or a fresh replay of the cited results.

## Scope and current findings

The source already states the completed milestone-115 theorem correctly in the abstract and at lines 2782–2811: a fitting canonical direction window \(012310\) has five-count sum at least \(19\), without extra count, endpoint-location or parity assumptions. All 1,397 modules are recorded as complete. This is distinct from the completed share floor \(12\) for the same shape, and from the unproved six-count floor \(25\) on \(0123104\). No passage was found explicitly calling the five-count theorem pending. The introduction and verification summary should nevertheless include it explicitly, because their current inventories omit this completed result.

The five remaining local-share targets remain \((16,18,16,16,16)\) for \(012032,012034,012301,012340,012345\). A complete native replay for the \(012301\) cap-15 Boolean formula is not yet an actual-snake share-16 theorem. At the reviewed milestone-145 cutoff, the 104 checked initial-database parts for the preserved share-18 proof were not a completed assembly. The coordinator subsequently reported successful milestone-146 original-CNF-to-chunk, initial-tree assembly and prefix-composition checks. The current revision must state that this specific initial-database bridge is complete, while retaining the earlier timeout as historical evidence. The complete share-18 replay and actual-snake interpretation remain unfinished. This review has not independently rerun those newly reported checks.

The current comparison obstruction is the joint restriction \(325F+159G>9074\) and the lower comparison \(235+95/2348\) when both selected floors are at most 16. Its fixed weights leave the eleven-cycle unchanged. The proposed \(012032\) share floor 16 adds 57 to that cycle and changes this hypothesis. Thus the obstruction does not refute the full conditional-234 profile. The maintained interval remains \(191\le a(9)\le235\), with the stated contributor-proof and independent-rebuild distinction.

## Required prose and status corrections

1. **Stale completion statement, lines 3162–3165.** The sentence saying that the new graph minimum has not yet been computed is immediately followed by its completed zero-credit computation. Replace its final two sentences with:

   > These statements identify the deleted cycles. Section~\ref{sec:zero-credit-exclusion} gives the completed zero-credit calculation for the resulting graph.

2. **Closure refers to a superseded obstruction, lines 3591–3598.** The discussion ends at the old two-cycle uniform-credit proposition even though that competing cycle has since been excluded. Retain that earlier theorem in the historical comparison appendix, and replace the current closure discussion with the joint-floor paragraph proposed below.

3. **The proposed-restriction evidence is described too generally, lines 2813–2821.** Some later restrictions have complete native replays while their Lean derivations remain incomplete. Replace the opening sentence with:

   > The remaining proposed restrictions have computational exclusions, while their complete Lean derivations remain unfinished.

   Preserve the following specific timeouts and local-forest evidence. This avoids identifying every unfinished actual-snake theorem with an unfinished native contradiction.

4. **Historical progress is presented as a current task, lines 3330–3344.** Replace “is the selected next local theorem target” with “remains one of the five local targets in the conditional profile”. The later joint analysis shows that the selected three targets must be considered together. Retain the 23-of-231 historical partial-proof count with an explicit date or stage qualification; do not present it as the current status of every share-18 attempt.

5. **Duplicate share-18 progress reports, lines 3407–3418 and 3532–3537.** Keep the full 144 and 145 certificate records together in a verification appendix, preserving all counts and limitations at their historical cutoffs. Incorporating the coordinator's milestone-146 result, use one current sentence:

   > The share-18 certificate has a complete independent Boolean replay. The original clause assignment now transfers through all 104 chunks to the preserved initial tree, and this transfer composes with the checked 1055-deduction prefix using 6006 propagation references. The complete Lean replay and actual-snake interpretation remain unfinished.

6. **Historical bibliography cutoffs, lines 6053–6055 and 6087–6089.** Statements that the endpoint-equality or stronger-occurrence theorem was pending are valid descriptions of their archived cutoffs. Keep those qualifiers; do not globally replace every occurrence of “pending”. The current results cite their later completed archives.

7. **Bibliography preservation.** The `totalcountarchive` URL is a pinned early record. The completed theorem also cites `share145archive`, which records completion. Preserve both. A later immutable completion reference would improve reproducibility only after the relevant revision has actually been verified; no new revision identifier should be invented.

## Mathematical and notation issues

No contradiction in the main square identity, the 235 deduction, or the milestone-145 joint-floor algebra was found during this source review. This statement reports the review result; it is not a certificate audit.

Two limited issues warrant correction independently of historical reorganisation:

- **Scaled potential units, lines 3862, 3889 and 3924.** The displayed rational quantities are called “integer means”. At line 3889, the comparison formula uses \(p=9891\), \(d=20\), and scaled potential range \(R=12101\). Therefore its unscaled mean is \(9891/20\), and its unscaled range is \(12101/20\). Replace the sentence by: “For the nine-transition forced-absence model, the unscaled mean is \(9891/20\); the potential certificate uses denominator 20 and scaled range 12101.” At line 3924 use “unscaled mean \(18823/38\)” and retain “range 23459 at denominator 38”. At line 3862 use “means” instead of “integer means”. These are unit/terminology corrections; the printed comparison fractions are consistent with scaled certificates.
- **Short-path boundary of an appendix proof, lines 4730–4739.** The proof of Proposition `prop:window-aggregate` uses \(\beta_0,\beta_1\) without first disposing of paths with fewer than two internal vertices. The claimed bounds remain immediate for these paths. Add: “For the first conclusion, paths with at most 242 edges already satisfy the claim; for the second, paths with at most 241 edges already satisfy it. In each remaining case all indexed internal counts below exist.” This repairs a proof-domain omission while preserving both statements. The larger \(8^3\) and \(8^4\) computational enumerations may include the unused symbol zero; the text should say “bounded encoded triples/quadruples” if explaining that count, rather than implying there are eight positive clamped values.

Additional notation changes should remain local. The paper uses \(r\) for a window's starting vertex except in Proposition `prop:three-excess`, where it expressly denotes the first internal centre. Preserve that qualifier if the block is moved. The letter \(C\) denotes an occurrence count in `cor:combined-budget`, a short-walk weight in older comparisons, and the uniform occurrence credit in the latest analysis. Give each section its existing meaning explicitly; a paper-wide renaming would create unnecessary proof and table changes. In the current joint-floor section, keep \(F,G\) as share floors and \(B=24\) as the occurrence allowance.

## Concrete reorganisation

Use mathematical dependence as the main order. Move whole statement/proof blocks, retaining their labels and all mathematical contents. No new named definitions are needed. The following arrangement is coherent and supports a substantially shorter main narrative:

| Main location | Existing blocks to retain there | Dependency requirement |
|---|---|---|
| Problem and results | 47–113 | Preserve the 235 contributor-proof qualification and add the completed 012310 count theorem to the status table. |
| Square census and local necessities | 114–193; normalization and finite conditions 196–219 | Put `lem:degree-forced` (1238–1243) here if moving the longer count results ahead of shares. |
| Upper bound 235 and direct improvement criteria | 220–387 | Preserve the complete 235 proof and all six-count/shortfall implications. |
| Local count and endpoint restrictions | 388–544; 693–1223; 1326–1371; 1372–1614; 2782–2811; 3022–3071; 3127–3166 | Keep each theorem with its full proof, sharpness qualification and citations. Put the completed 012310 theorem alongside the other count-sum theorems. The count-24 proof depends on the common-neighbour result and the earlier count-32 assignment; preserve that dependency. |
| Empty-square shares | 545–692; 1224–1325 excluding the moved degree lemma; 1615–1678 | Keep the share definition, loss identity and packing lemma before all share theorems. The shape classification and completed/pending floors remain together. |
| Common budgets and boundary estimates | 1679–1777; 1797–1916 | Preserve the factor-seven and five-position capacities, the conditional finite-block proposition, and the boundary-21 proof. |
| Finite graph interpretation and conditional 234 | 1917–2582; general bonus criterion 2626–2686 | Keep exact-history recognition before compatible-word coverage; preserve full-key edge identity before weight and total-charge assembly. Retain the complete pending-floor table. |
| Current fixed-graph limitations | 3346–3538, with compact cross-references to the nine-cycle and earlier profiles; 3539–3561 | State the precise graph, weights and occurrence event before the joint-floor propositions. Retain the eleven-cycle base total 5399 and four events, the fourteen-cycle weights, the two-edge range bound, and the 57-unit change under 012032 floor 16. Move certificate implementation chronology to the verification appendix. |
| Remaining requirements and verification | 3562–3603; 3805–3854, using the replacements below | Present completed actual-snake results, conditional graph obligations and current certificate status once. |

The following material belongs in appendices. Its mathematical content and labels must remain intact:

- Move the earlier seven-centre model, lines 1778–1796, beside `app:replacement-cycle` and `app:six-count-cycle`. Its mean \(42/11\), potential range 8064, 4,551,730-edge verification and exact cycle remain available without interrupting common-budget proofs.
- Move the coarse weakening experiments, lines 2583–2625, and the baseline unsaturated-cycle analysis, 2687–2750, into the existing finite-model appendix. Preserve `prop:short-walk-obstruction`, `prop:unsaturated-cycle`, their tables and proofs. They remain valid for those graphs, though they no longer describe the current refined graph.
- Make one appendix for the chronology of count-sum and uniform-credit refinements. It should contain 2751–2781, 2812–3021, 3072–3126, 3167–3345, and any proof-progress paragraphs relocated from 3407–3418 and 3521–3537. Keep the ten-rule table, every proposed rule, all comparison fractions, all cycle weights and every theorem/proposition proof. Add a short stage table stating which graph and share profile each recorded cycle belongs to. The proved local statements extracted above should be replaced in this appendix by cross-references, preserving each statement once.
- Move 3604–3642, the longer-term charge targets, the six-fours conjecture and the singleton-density limitation, into a clearly identified research-target appendix. Preserve the conjecture and all propositions/proofs exactly apart from necessary navigation prose.
- Move 3643–3804, the numerical 196 conjecture and construction/optimality criteria, before the existing construction experiments 5061–5433. Keep `sec:hypothesis`, `sec:optimality`, all theorem labels, recurrence formulas, joining conditions, and cited results. The introduction and final verification paragraph still state that 196 is unresolved.
- Preserve the existing historical bounds, all three longtables, all 16 quote environments containing transition strings, every explicit vertex list, blocker index and bibliography entry. Their relative order can remain unchanged.

Whenever a section moves across `\appendix`, replace narrative “Section” references with “Appendix” as appropriate while preserving `\ref` labels. A source-level preservation audit should compare the multiset of theorem/proposition/lemma/corollary/conjecture statements, complete proof blocks, labels, mathematical displays, witness blocks, table rows and citation keys. A statement moved out of the main text must not be silently removed because it is weaker than a later theorem.

## Exact proposed summary prose

### Abstract

Replace the existing abstract prose, leaving the environment and preamble unchanged:

> Let $a(9)$ be the maximum edge length of an induced path in the nine-dimensional binary hypercube. An explicit construction and an archived contributor proof give $191\le a(9)\le235$; a complete independent rebuild of the upper-bound proof remains pending. For a snake of length $m$, total singleton-square count $T$ and empty-square count $s_0$, the identity $T+2s_0+35(m+1)=9214$ supports count and share estimates. Completed local results include the sharp pair bound eight on $012032$, its endpoint and parity consequences, a bound of twenty-four low-pair windows, and a five-count sum of at least nineteen on $012310$. Direct six-count and empty-square criteria give conditional improvements to 234 and 233. A separate finite-graph comparison reaches 234 under five unfinished share bounds and explicit reference and potential-certificate premises. For the retained completed-share graph, two saved cycles impose $325F+159G>9074$ on the share floors for $012301$ and $012340$ if the eleven-cycle remains unchanged. Floors at most sixteen leave the comparison above 235. The proposed $012032$ floor changes that cycle, so the full conditional profile remains unresolved. The optimum and the numerical conjecture 196 remain open.

All details omitted from this condensed abstract remain in their theorem/proof blocks.

### Introduction and evidence table

Replace the roadmap paragraph at line 86 after the moves with:

> The proof begins with the square census and the archived six-centre argument for 235. Direct six-count criteria then state sufficient conditions for 234 and 233. Local count and endpoint theorems provide the geometric restrictions used by the empty-square shares and their common overlap budgets. The finite comparison graph is treated through exact history recognition, coverage of actual state walks, edge-weight interpretation and the boundary estimate. The conditional 234 comparison retains its five local share premises, reference refutations and complete potential certificate. The current cycle analysis identifies joint requirements on further shares. Earlier model calculations, construction experiments, the numerical conjecture and all explicit witnesses are retained in the appendices.

Add the following row to the evidence table, preserving every existing row:

> Five-count sum on $012310$ & The sum of the five internal counts is at least 19. All 1397 modules, including the actual-snake deduction, have completed checks; no extra count, endpoint-location or parity premise remains.\\

Replace the table's “Conditional bound 234” evidence cell with:

> Slope 496, range 602 and boundary contribution 21. Five local shares, the remaining 1358 reference refutations and the complete finite potential certificate are still required.

The words “still required” concern the independent share argument, rather than withdrawing the separately archived contributor upper bound of 235.

### Closure

Retain the three-item list of reference, potential and share obligations at lines 3566–3583. Replace the opening paragraph with:

> The maintained interval is $191\le a(9)\le235$, with the contributor-proof and independent-rebuild distinction stated in Section~\ref{sec:verification}. The direct route to 234 requires a universal six-count floor, the stated shortfall bound, or one of the joint count and empty-square assumptions. The proved $0123041$ class, the $012310$ five-count theorem and the necessary $0120324$ intervals do not establish any of those universal premises. The separate share argument has checked graph coverage and weight interpretation under its stated assumptions. Its remaining obligations are as follows.

Replace lines 3591–3598 with:

> Proposition~\ref{prop:least-floors} identifies the least sufficient integer floors within its fixed box. The earlier slope-and-range comparisons remain valid for their specified profiles; they do not determine the least range for the reduced $012034$ floor 18. For the current retained graph, Proposition~\ref{prop:two-cycle-share16-obstruction} gives a comparison of at least $235+95/2348$ when the $012301$ and $012340$ floors are at most 16 and the eleven-cycle remains unchanged. The necessary relation is $325F+159G>9074$. The existing $012032$ share-16 target adds 57 to the eleven-cycle and removes the unchanged-weight hypothesis. These three local targets therefore require a joint analysis, followed by the remaining graph and proof obligations. Stronger geometric restrictions, boundary accounting or conditions on actual initial and final states can change the comparison.

Preserve the separate contributor seven-centre proposal paragraph and its citation. Keep the stated strict margin 30 and all five target values in the preceding conditional-profile discussion.

### Verification

Retain the first paragraph at 3806–3812 and replace the remainder with the following concise status summary, placing full numerical receipts in the verification appendix:

> In the newer share argument, actual windows have consistent full direction, history and count keys. Coverage of the accepted-key graph, all 55 history-share rules, the other baseline weight components, and the boundary and total-charge deductions have passed Lean under their stated premises. Twenty of the 1378 reference entries have checked refutations; 1358 remain. Exact-integer scans verify the two saved potentials on all 4947008 accepted keys, while the complete Lean edge certificate remains unfinished. The conditional 234 profile additionally requires share floors $(16,18,16,16,16)$ for $012032,012034,012301,012340,012345$.
>
> The completed actual-snake results include the sharp $012032$ pair inequality, its equality geometry and parity consequence, the parity-free endpoint implication, the twenty-four-window bound, the $0123041$ six-count bound, the restrictions on low-total $0120324$ windows, and the nine-transition and five-count exclusions. The five-count sum at least 19 on $012310$ is also complete: all 1397 proof modules and their saved dependencies have been audited. This theorem has no additional count, endpoint-location or parity premise. The direct shortfall implication is checked, while its sufficient universal upper bound remains unresolved.
>
> The $012301$ share-16 target has a complete independent Boolean replay of 285541 deductions and 31017505 propagation references from 12977 original core clauses. Its complete Lean replay, cycle-clause interpretation, coordinate transfer and reversal remain required. For the preserved $012034$ share-18 proof, the original-clause assignment now transfers through all 104 chunks to the materialized initial tree and composes with the checked 1055-deduction prefix using 6006 propagation references. The preceding assembly timeout is retained in the historical record. The remaining full replay and actual-snake interpretation are unfinished. These records establish progress on certificates without completing either local share theorem.
>
> The saved-cycle obstructions concern their stated graph, weights and occurrence event. In particular, the joint-floor obstruction leaves the eleven-cycle unchanged, whereas the proposed $012032$ floor 16 raises its total by 57. It therefore leaves the full conditional 234 profile unresolved. No construction above 191 or matching optimality theorem has been obtained. The numerical conjecture 196 is used in none of the proved bounds.

The new summary must retain suitable existing archive citations, especially `referenceunionarchive`, `potentialcertificatearchive`, `count24archive`, `fivecount140archive` and `share145archive`; moving a cited technical paragraph does not authorize deleting its citation. The new milestone-146 bridge result needs the coordinator's verified source and receipt reference before publication. Reported successful checks are `RawChunksAssoc146` (5.641 seconds; `propext`), `AssemblyAssoc146` (13.562 seconds; `propext`, `Quot.sound`) and `PrefixAssoc146` (2.859 seconds; standard axioms). These data were supplied during the review and were not independently rerun by this reviewer.

## Coverage and source-only checks

Read ranges, inclusive: 1–390; 391–820; 821–1224; 1225–1679; 1680–1917; 1918–2226; 2227–2583; 2584–2884; 2885–3234; 3235–3562; 3563–3945; 3946–4284; 4285–4514; 4515–4869; 4870–5205; 5206–5434; 5435–5754; 5755–6126. The first output for 1225–1679 had a short truncation near `prop:joint-singleton-excess`; lines 1459–1489 were reread completely, closing that gap.

Static source inventory: 261 labels, no duplicate labels, no unresolved `ref`/`eqref` targets, 63 bibliography entries and no unresolved citation keys. There are 49 theorem, 68 proposition, 29 lemma, 14 corollary, two conjecture, one definition and 158 proof environments; the three-count geometric classification is explicitly an outline outside a proof environment. There are 16 quote environments and three longtables. These counts support preservation checking only. They do not verify the mathematics, external source claims, rendering or certificate validity.

The memory registry was consulted only to identify the project's evidence-preservation convention. Baseline statuses come from the inspected source and milestone-145 records; the later bridge update is explicitly attributed to the coordinator's milestone-146 report.
