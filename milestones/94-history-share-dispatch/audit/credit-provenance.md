# History-share credit provenance

Current status at audit close: the parent has checked milestone 94 coverage, assembly, validity, counts and cap transport, totalling 73 theorem audits. Actual compatible-window coverage and generic numeric cap transport are discharged. Concrete credit instantiation, compatible imports, and the linked maximum dispatch remain open.

All 55 share rules in milestone 67 have a matching historical local lower-bound theorem for every compatible word recorded by milestone 94's complete Python enumeration. This audit identifies 69 geometric word bounds and eight stronger count-conditioned bounds, using 77 selected `in_snake` theorems in 29 source modules. Forty-two selected milestone 67 wrappers reuse milestone 61 geometry; their underlying words, bounds, sources and printed theorem dependencies were checked separately across ten source modules.

This is a source and provenance audit. This auditor started no Lean compiler, solver, replay or graph search. During the audit, the parent completed milestone 94's 16 modules and 73 theorem audits; their source, object and log hashes were inspected here. Those modules prove the compatible-word coverage and dispatch interfaces under explicit per-word credit premises. The concrete historical credit port and a new snake bound remain unproved. The exact word-to-theorem map, theorem statements, source lines, historical receipts, current object/log hashes and import observations are in `data/credit-provenance.json`.

## Credit convention and actual positions

Let $p$ be a snake with $m$ edges, let $r+9\le m$, and suppose a three-direction-ID signature is emitted at edge position $r$. The checked history transport gives $r\ge2$. Write

$$
a=r-2,\qquad w=\operatorname{canon}(\operatorname{dsOf}(p,a,11)),\qquad
S_r=\sum_{i=0}^{4}\sigma_{12}(p,r+4+i).
$$

Here $\sigma_{12}$ is exactly `coreShare 12`, the integer share at scale 12. The local eleven-word theorems charge offsets $6,7,8,9,10$ from $a$. These are the actual centres $r+4,\ldots,r+8$. All credits in the tables below are lower bounds on $S_r$ in these integer units. Alternative lower bounds on the same sum are combined by their maximum; they are not added.

The six count symbols have positions $r+3+k$, for $0\le k<6$. A cap at index $k$ becomes the local eleven-window bound at bounds-list index $4+k$, whose centre is $a+(4+k)+1=r+3+k$. Every used cap is below 6: the values are 1, 2 or 5. Thus the checked `truncated_guard` equivalence converts the symbol cap into the exact count cap. All other ten local bounds are $0\le\alpha\le21$, provided by natural-number nonnegativity and `coreAlpha_le_21`. Symbol 6 retains its interval meaning $[6,21]$.

## Eight legacy rules

The old model stores one `directions` field for each of these rules. That storage format does not prove uniqueness. The milestone 66 builder explicitly screened recognition against all generated eleven-word shapes; independently, milestone 94's current Python enumeration returns exactly one compatible word for each of these eight signatures. The newly checked `saved_variant_iff_fits` now identifies the saved lists with the precise local compatibility predicate. Uniqueness follows from that characterization together with the singleton list, rather than from the old storage format.

All theorem names below have prefix `Snake9.LocalWindow.` and suffix `.in_snake`. The count-conditioned theorem belongs to `CountPropagation65` and requires its full ten-entry bounds premise.

| Legacy edge | Signature | Geometric credit and theorem | Capped credit and theorem | Six-count caps |
|---:|---|---|---|---|
| 7 | `[54, 300, 99]` | 18, `NeighbourChoice64.E007` | 19, `CountPropagation65.E007` | $c_{1}\le 2$, $c_{2}\le 2$ |
| 10 | `[66, 438, 302]` | 32, `NeighbourChoice64.E010` | 36, `CountPropagation65.E010` | $c_{0}\le 2$ |
| 11 | `[66, 439, 299]` | 11, `NeighbourChoice64.E011` | 15, `CountPropagation65.E011` | $c_{0}\le 2$ |
| 44 | `[177, 54, 300]` | 10, `FamilyShare61.G154` | 13, `CountPropagation65.E044` | $c_{2}\le 2$, $c_{3}\le 2$ |
| 45 | `[177, 55, 301]` | 19, `LongWindow63.E045` | 26, `CountPropagation65.E045` | $c_{2}\le 2$, $c_{3}\le 2$ |
| 57 | `[258, 350, 180]` | 22, `LongWindow63.E057` | 26, `CountPropagation65.E057` | $c_{3}\le 2$ |
| 58 | `[258, 354, 180]` | 6, `SplitShare62.E27` | 12, `CountPropagation65.E058` | $c_{3}\le 2$ |
| 91 | `[350, 181, 73]` | 4, `FamilyShare61.G200` | 5, `CountPropagation65.E091` | $c_{0}\le 1$, $c_{3}\le 5$, $c_{4}\le 1$ |

Edge 58 needs a suffix step. Its eleven-word representative is $(0,1,2,3,4,0,3,2,5,6,3)$. The canonical final nine directions are $(0,1,2,3,1,0,4,5,1)$. The theorem `SplitShare62.E27.in_snake` proves a geometric credit of 6 on these nine directions, charging offsets $4,\ldots,8$ from their start $r$. Its centres therefore coincide with $S_r$. The eleven-word geometric tables themselves give zero before this inherited suffix credit. Milestones 63 and 64 did not generate a separate edge-58 geometry theorem because their candidate 6 equalled the inherited bound. The capped credit 12 is supplied independently by `CountPropagation65.E058.in_snake`.

The other seven geometric entries use eleven-word theorems. Each of the eight capped bounds was checked against the actual source `bounds` list: the list has length ten, lower endpoints zero, and precisely the model's upper caps at indices $4+k$; every other upper endpoint is 21.

## Forty-seven later rules

These rules have no count caps. Their credit is the minimum of the local bounds over all compatible variants. In the following table, `Gxxx` means `Snake9.LocalWindow.FamilyCharge67.Gxxx.in_snake`. The JSON records the complete word corresponding to every entry, so the order of variants is explicit. Each listed theorem proves at least the displayed rule credit; a stronger variant theorem is weakened by arithmetic when needed.

| Model index | Edge label | Signature | Rule credit | Variant theorems |
|---:|---:|---|---:|---|
| 11 | 2000 | `[26, 215, 79]` | 2 | `G000` |
| 12 | 2001 | `[27, 219, 34]` | 4 | `G001` |
| 13 | 2002 | `[27, 219, 35]` | 4 | `G002`, `G003` |
| 14 | 2003 | `[29, 235, 79]` | 2 | `G004` |
| 15 | 2004 | `[35, 350, 180]` | 20 | `G007` |
| 16 | 2005 | `[35, 351, 172]` | 6 | `G005`, `G006` |
| 17 | 2006 | `[90, 139, 350]` | 9 | `G008` |
| 18 | 2007 | `[90, 139, 354]` | 9 | `G009` |
| 19 | 2008 | `[99, 147, 460]` | 2 | `G010` |
| 20 | 2009 | `[99, 147, 461]` | 2 | `G011` |
| 21 | 2010 | `[99, 147, 462]` | 2 | `G012` |
| 22 | 2011 | `[139, 350, 179]` | 13 | `G013` |
| 23 | 2012 | `[147, 460, 350]` | 8 | `G015` |
| 24 | 2013 | `[147, 460, 351]` | 16 | `G014` |
| 25 | 2014 | `[147, 460, 352]` | 12 | `G016` |
| 26 | 2015 | `[147, 460, 354]` | 16 | `G017` |
| 27 | 2016 | `[175, 50, 264]` | 5 | `G018` |
| 28 | 2017 | `[177, 55, 305]` | 13 | `G019` |
| 29 | 2018 | `[215, 79, 462]` | 2 | `G020` |
| 30 | 2019 | `[219, 34, 348]` | 5 | `G022` |
| 31 | 2020 | `[219, 35, 351]` | 4 | `G021`, `G023` |
| 32 | 2021 | `[235, 79, 462]` | 2 | `G024`, `G025` |
| 33 | 2022 | `[264, 395, 460]` | 2 | `G026` |
| 34 | 2023 | `[264, 395, 462]` | 2 | `G027` |
| 35 | 2024 | `[281, 460, 354]` | 7 | `G028` |
| 36 | 2025 | `[302, 90, 139]` | 16 | `G029`, `G030` |
| 37 | 2026 | `[305, 99, 147]` | 4 | `G031` |
| 38 | 2027 | `[350, 182, 78]` | 4 | `G032` |
| 39 | 2028 | `[351, 171, 35]` | 7 | `G034`, `G035` |
| 40 | 2029 | `[351, 172, 39]` | 6 | `G033`, `G036` |
| 41 | 2030 | `[353, 177, 55]` | 14 | `G037`, `G038` |
| 42 | 2031 | `[354, 181, 73]` | 5 | `G039`, `G040` |
| 43 | 2032 | `[354, 182, 78]` | 5 | `G041`, `G042` |
| 44 | 2033 | `[395, 460, 354]` | 7 | `G043` |
| 45 | 2034 | `[426, 281, 460]` | 2 | `G045` |
| 46 | 2035 | `[426, 281, 462]` | 2 | `G044`, `G046` |
| 47 | 2036 | `[440, 302, 90]` | 15 | `G047` |
| 48 | 2037 | `[460, 350, 183]` | 10 | `G048` |
| 49 | 2038 | `[460, 352, 175]` | 4 | `G049` |
| 50 | 2039 | `[462, 350, 180]` | 20 | `G051` |
| 51 | 2040 | `[462, 350, 181]` | 10 | `G052` |
| 52 | 2041 | `[462, 350, 182]` | 10 | `G053` |
| 53 | 2042 | `[462, 350, 183]` | 20 | `G050`, `G054` |
| 54 | 2043 | `[462, 353, 177]` | 13 | `G057` |
| 55 | 2044 | `[479, 395, 460]` | 2 | `G059` |
| 56 | 2045 | `[479, 395, 462]` | 2 | `G058`, `G060` |
| 57 | 2046 | `[496, 460, 354]` | 16 | `G061`, `G062` |

The complete enumeration has 11,162 canonical induced eleven-word shapes, 69 distinct compatible words for these 55 rules, and 14 rules with two variants. All 47 stored variant lists agree with the new enumeration as sets. The eight legacy representatives occur in the enumeration. The Python facts are pinned by the input hash. The new checked `saved_rule_emitted_word_mem` additionally proves that every actual emitted window belongs to the saved list, and `saved_variant_iff_fits` characterizes the complete compatible set. Checked count theorems give 41 singleton lists and 14 doubleton lists, with total length 69.

## Transport to a genuine snake

The reusable proof can be separated into four small statements.

1. **Coordinate realization.** For any fitting direction window, its first-occurrence canonicalization is obtained by a coordinate permutation. The proof already used by `CountFreeAdapter73.canonical_share_bound` constructs the list of used coordinates with `seenAfter`, proves it is duplicate-free and has length at most nine, and applies `mkPerm_spec`. Its coordinate argument generalizes from six directions to arbitrary window length without a finite geometry calculation. The resulting permutation supplies exactly the `hP` premise expected by each `in_snake` theorem.

2. **History recognition.** `History84.emitted_three_actual` identifies the last three actual direction IDs and proves $r\ge2$. `History84.emitted_three_canonical_slices` identifies those IDs with the three canonical nine-slices of $w$. The newly checked `saved_rule_emitted_word_mem` now shows that $w$ equals one of the listed words. The finite covers and `saved_variant_iff_fits` cover both possibilities for all 14 multiple-variant rules. This part is complete.

3. **Local credit transport.** For an eleven-word match, invoke the corresponding theorem at $a=r-2$, using $a+11=r+9\le m$ and the coordinate realization. Arithmetic changes its centre expression to $S_r$. For edge 58's geometric credit, first use `History84.canonical_window_slice` with slice offset 2 and width 9, then realize the canonical final-nine word and invoke `SplitShare62.E27.in_snake` at $r$. For a capped theorem, construct its ten bounds using the index relation above. The numeric cap-to-actual conversion is already checked in `numeric_caps_to_actual`; the ten-bound adapter to the historical theorem is still needed. No reversal is needed because every oriented canonical variant is stored explicitly.

4. **Maximum of applicable credits.** Define each rule's contribution as zero when its signature is absent, its geometric credit when the signature is present, and the maximum of that geometric credit and its capped credit when all caps hold. Each contribution is at most $S_r$. A finite maximum over the 55 contributions is consequently at most $S_r$. Retain the history state, direction index and six-count code in the rule lookup; direction alone does not determine whether a history signature is emitted.

The smallest useful remaining concrete implementation is a generic coordinate-realization/credit-transport lemma followed by the single-word rule with edge label 2000 (`FamilyCharge67.G000.in_snake`, credit 2). It exercises actual history, the eleven-word match and the exact five-centre shift without a count-cap premise. The same interface then supports all 69 geometric word cases; the eight capped cases add one ten-bound conversion lemma. A further wrapper takes the finite maximum. The new `saved_rule_five_centre_share` and `emitted_capped_share_of_numeric_test` already provide the actual-window dispatch once their explicit `WordShareBound` or `WordCappedShareBound` premises are supplied. This audit supplies the historical source map for closing those premises in the current environment; it does not claim that credit port has been checked.

## Import compatibility and receipt limits

The historical modules cannot be treated as an already verified combined import environment.

- The current milestone 92 search path resolves none of the selected geometry/count instance modules or their legacy generic support modules. Those paths must be supplied or sources ported.
- Five selected module names collide across milestones: `Edge007`, `Edge010`, `Edge011`, `Edge045` and `Edge057`. Their theorem namespaces differ, but their import module names are identical. Ordinary search-path ordering selects only one object for each such name.
- Legacy geometric support ultimately imports milestone 51 `ShareFrame`. The current state/history environment uses milestone 72 `LocalWindowShareBridge`. These independently declare 14 common names in `Snake9.LocalWindow`, including `coreShare`, `shareLocal_frame` and `refuted_share_bridge`. The definition text of `coreShare` is identical, but the full source files and module identities differ. This is a declaration-ownership conflict that must be resolved before combining the developments.
- The old and current paths resolve `LocalWindowDirBridge` and `DirectionWindowBridge` to the same milestone 32 objects. Thus the inspected low-level direction bridge agrees; that observation alone does not check the entire combined environment.

A practical integration uses distinct module names for copied instances and generic support that imports the current share bridge. The corresponding generic proofs and selected instances must then be checked in that one environment. Avoid claiming that renaming an object file or reordering old paths establishes compatibility. In particular, merely changing an import in a generic source does not revalidate historical compiled dependants.

For every selected local theorem, this audit checked that the current source SHA-256 equals its successful historical receipt, that its build record reports exit code zero for those source bytes, that the corresponding object exists, and that the log prints only `propext`, `Classical.choice` and `Quot.sound` as possible dependencies. The 42 underlying reused geometry theorems were also matched to their exact source word, sufficient lower bound and printed audit. Historical receipts pin source hashes but do not pin these object hashes. The JSON records current object and log hashes for reproducibility; it does not retroactively extend the historical trust record. No full dependency closure was rehashed or rebuilt.

The remaining integration work is canonical transport of the concrete historical credits, the ten-bound cap adapter, and the maximum evaluator linked to the saved rule order in a compatible environment. Actual-window coverage and numeric cap transport are complete in the inspected milestone 94 receipts. No extra local geometric lower bound is missing from the inspected 55-rule model. Full graph weights, endpoint accounting, a potential certificate, and any remaining separate local-floor premises remain outside this audit.

JSON SHA-256: `a04fc7d5ac70d9e751c5fe6a918efc4b1784a5292eded41da7bbdeb252e73c1e`.
