# Round 210 review: manuscript lines 1–3300

## Coverage and limits

Read every line 1–3300, inclusive, of `milestones/210-paper-review/data/research-before.tex`. The successful reading chunks covered 1–1250, 1251–1500, 1501–1800, 1801–2100, 2101–2400, 2401–2700, 2701–3000, and 3001–3300. An earlier truncated request for 1251–1650 was discarded and that interval was reread completely. Line 3300 ends a proposition; its following proof lies outside this assignment.

This was a mathematical and proof-status review. No compiler, solver, search, or software tests were run. No manuscript was edited. Selected archived source and logs were read to assess the 235 theorem. The review does not independently verify every cited certificate, dependency, or native enumeration.

## Overall assessment

No definite false theorem or invalid algebraic implication was found in the assigned text. The distinction between a universal snake statement, a finite comparison-graph statement, a local feasible forest, and a native restricted search is generally explicit and appropriate. The manuscript should retain those distinctions during compression. The principal corrections concern proof provenance and obsolete intermediate status statements, rather than a newly found mathematical counterexample.

## Archived upper bound: preserve the result and identify the evidence

Anchors: lines 39–42, 138–146, 168–183, 331–381; citation `bound235archive` at lines 9802–9804 was inspected as a decisive source pointer outside the assigned interval.

The archived 235 result has substantially more evidence than an unassembled conditional estimate. At the exact cited revision `b20346ee15a43b96de34128bc66b05551244cf31`, the file `work/spectral/stronger/UpperBound235.lean` contains:

- `allRefuted6K235`, assembled from the contributor refutation families;
- `upper_bound_235 {m : Nat} (p : Snake m) : m ≤ 235`, with no remaining local-refutation argument;
- `verified_interval_191_235`, combining the witness and the universal bound.

At that same revision, `outputs/upper-bound-235-audit-linux.log` ends with successful compilation of `UpperBound235`, exit 0, and reports only `propext`, `Classical.choice`, and `Quot.sound` for the two final results. The preserved contributor replay report in `milestones/51-exact-bucket-pressure/data/contributor/upper-bound-235-replay-linux.log` records the 635 new roots and their completed replay closure. The assembly audit reuses dependencies; it is not an independent clean rebuild of all those dependencies. Reading these records does not recreate the archived kernel run.

**Recommended treatment:** retain the attributed archived theorem and boxed interval. Do not silently replace the upper bound by an unproved conjecture merely because independent reproduction remains pending. Equally, do not describe this review as a fresh independent check of the entire theorem. A concise replacement for the status sentence at lines 143–146 is:

> The upper bound is the completed contributor theorem `Snake9.upper_bound_235` at the cited archival revision. Its saved compilation and axiom audit are successful. The present work has inspected that assembly and independently reconstructed its finite potential; a clean independent rebuild of the complete dependency closure remains pending.

Lines 343 and 364–365 correctly separate the archived walk theorem from the newer checked boundary implication. Keep that dependency visible when stating the strengthened inequality `39m + 2s_0 ≤ 9192` and its consequences. The improved 14-empty-square criterion inherits the archived catalogue/walk result; it is not an independently rebuilt alternative proof of 235.

The current 1378-key reference interface is a different package. Lines 2521–2525 correctly explain why its 1358 outstanding entries do not contradict completion of the archived 235 theorem. This explanation is essential and should appear near the principal status table as well as in the technical graph section. Do not transfer the archived result to a different local-system interface without its semantic bridge.

## Anchored corrections and consolidation

1. **Superseded Lean-status sentence, lines 781–785 versus 863–876.** The earlier paragraph says the complete interpretation of the undominated-vertex argument in `Q_9` remains to be assembled. The later text records a completed actual-cube/path bridge for the stronger conclusion `e(q) ≥ 8`. The weaker `e(q) ≥ 5` and loss-59 consequences then follow from the stronger result. Retain the earlier proof if useful, but label its partial implementation as historical and point to the later completed stronger theorem. Otherwise a reader can reasonably infer that the current geometric bridge remains open.

2. **Earlier potential criterion presented after its improvement, lines 2292–2324.** These formulas correctly use the older boundary 21, but their titles do not consistently indicate that restriction. Mark the corollary and loss proposition as the boundary-21 comparison, or lead with the already proved boundary-24 version and move the older constants to the historical discussion. Under the same walk/weight hypotheses, boundary 24 gives `(p + 4200d)m + 5dL ≤ 1098600d + 8p + R`; the strict exclusion condition at 235 is `227p > 111600d + R`. This is an algebraic consequence of lines 2260–2289, not a newly completed local-floor or potential certificate.

3. **The principal edge-weight theorem retains an older total, lines 2720–2759.** Its boundary-21 statement is valid, but the preceding boundary-24 theorem already yields `W + 2880 ≤ 5G_12` and `W + 4200m + 5L ≤ 1098600` for the same completed local floors. Present the stronger current total first. Preserve the weaker totals when explaining archived numerical profiles. Updating this arithmetic must not turn the reference-union and complete-potential premises into established facts.

4. **Current and historical floor profiles, lines 2037–2054, 2695–2718, 2807–2927.** The nine-shape table explicitly says it records original targets, and the exact least-floor theorem is correctly restricted to its fixed graph and boundary. Keep those qualifications. For a rewritten main narrative, show the current four pending floors `(15,14,14,14)` first, with the other proof obligations alongside them, and relegate the earlier `(18,16,16,16)`/boundary-21 optimization to a clearly historical subsection. The claim that 18 is least sufficient is true only for the earlier fixed comparison, as the text itself explains.

5. **Occurrence bounds, lines 1313–1503.** The sixteen-per-endpoint and thirty-two-total arguments remain correct intermediate results, but the current proved bounds are twelve and twenty-four. The headline discussion should state twenty-four and explain sixteen/thirty-two only as proof stages. The distinct thirteen-occurrence result for pair sum eight and both endpoints must remain separate. The manuscript correctly warns against applying it to each one-endpoint group, and that warning should survive revision.

6. **Source status counts, lines 2337 and 2513–2556.** These are counts for a particular exact-reference package, not the entire contributor project. The current handoff reports further contributor build progress on another revision, without an independent rebuild or interface transfer. Do not update 20/1378 or 1358 merely from that contributor module count. Attach the package identity/date to these counts when describing them as current.

## Mathematical checks worth preserving

- Lines 196–213: the square census, `s_3 = v − 2`, and `T + 2s_0 + 35v = 9214` agree for nontrivial paths. The endpoint and internal conventions remain consistent.
- Lines 346–394: the boundary sum yields `4m ≤ T + 13`, then `39m + 2s_0 ≤ 9192`. At `m = 235`, `2s_0 ≤ 27`, hence `s_0 ≤ 13`. The threshold 14 is correct.
- Lines 398–502: the disjoint-six-window and total-shortfall arithmetic uses the correct numbers of groups and uncharged vertices. The statements retain their universal-floor premises; local satisfiability and time limits do not establish those premises.
- Lines 671–728: the exact loss identity handles zero selected degree separately. The nonzero remainder classes for resolution 12 are correctly identified. Multiplicity of physical square incidences is essential.
- Lines 794–876: the missing-pair component argument uses a nonempty selected subset closed under selected adjacency and connectedness of the whole snake. Its stronger domination consequence is a substantive current result. The disconnected length classification is separately labelled as written geometry.
- Lines 1258–1503: the common unselected neighbour is stronger than the two distance equalities and is used in the endpoint occurrence count. The missing-pair capacity and finite residual case in the twelve-start proof do not justify dropping that hypothesis.
- Lines 1572–1668: enlarging the selected set lowers the shares, justified absences raise the derived lower bound, and alternatives on the same charged centres combine by a maximum. Count saturation respects the 21-corner universe.
- Lines 1784–2198: common excess and share budgets correctly bound overlap before adding bonuses. Conditional finite-block statements keep their count/share premises explicit.
- Lines 2330–2687: full edge keys are necessary because endpoint pairs do not identify the weight. The longest listed suffix argument needs the stated prefix closure. Emitted histories still need complete compatible geometric-word coverage; the text supplies that separate obligation. Clipped count six is an interval, and sum filters explicitly guard against treating it as an exact count.
- Lines 2858–3030: the least-floor obstruction and zero-bonus critical-cycle criterion are sound for the fixed finite graph. Neither establishes realizability of a graph cycle as a snake, a bound on potential range after arbitrary changes, or a universal local share floor.
- Lines 3146–3300: retained-graph obstructions keep their graph, boundary, floor profile, and occurrence allowance fixed. Those qualifications prevent historical impossibility statements from being mistaken for obstructions to the newer boundary-24 method.

## Recommended final proof-status summary

Use four explicit categories in the rewrite: (i) completed archived contributor theorem with saved audit, independent rebuild pending; (ii) present checked implications with named premises; (iii) independently checked native finite calculations; (iv) unresolved geometric/certificate premises. The reviewed text already contains these distinctions, but the long sequence of historical improvements makes the current dependency chain harder to identify. Compression should preserve hypotheses and provenance rather than merge those categories.
