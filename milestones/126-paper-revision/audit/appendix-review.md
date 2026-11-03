# Appendix and reference review for revision 126

## Scope and source

The complete assigned segment, lines 2650–4776 inclusive, was read: 2,127 lines, including the historical models, geometric arguments, all 175 catalogue rows, construction experiments, local diagnostics, all printed witnesses, all 55 history-share rows, and the complete bibliography. Line references below identify the pre-revision source `paper/snake9_research.tex`, SHA256 `5e62b785321b8b624338e484560f3ac16d048699c841deeccc69573fd13be72f`. The source had 4,776 lines throughout the inspection. One initially truncated display was recovered with a separate read of the affected lines 3991–4020; no assigned interval was omitted.

No manuscript, proof source, earlier evidence, or live batch was changed. No solver or compiler was run. This review includes small independent finite witness checks and checks of the three recent witness receipts. It does not replay the historical contradiction certificates, rerun graph enumerations, or verify remote bibliography contents.

## Main conclusion

Preserve all existing mathematical statements, catalogue entries, transition sequences, vertex lists, and historical numerical results. No incorrect printed witness was found. The historical diagnostic cases remain useful and are generally labelled accurately: local forests need not extend to a complete snake; a saved cycle does not by itself establish a minimum; restricted infeasibility is not a global exclusion; and a timeout gives no exclusion.

The necessary addition is a separate subsection containing the three complete sharpness witnesses for the new six-transition pattern $012032$. These should not replace the older 143/138-edge distance-three examples or the 140/146/148-edge endpoint examples, which establish different statements.

## Concrete editorial recommendations

| Original location | Recommendation and reason |
|---|---|
| Lines 2704–2716, earlier history model | Keep the ambiguous-word example. At line 2716 change the reference to omission from “the complete model” to omission from “this earlier model”, and add a cross-reference to the later complete compatible-word catalogue. The current 55-row catalogue already handles every compatible word; the older omitted-rule explanation must retain its historical scope. |
| Lines 2819–2857 and 3585–3661, archived upper-bound proofs | Preserve the recorded historical proof claims and pinned citations. Distinguish them from the current reference-union reconstruction: progress in recovering the exact union neither invalidates the historical statement nor certifies every current imported reference. Do not substitute the count of recovered union entries for a historical catalogue size. |
| Lines 2859–2884, small pair-cap catalogue | Preserve every row and the stated restriction to caps in $\{2,3\}^2$. The stronger new $012032$ result does not contradict maximality inside that restricted cap set. A cross-reference to the new pair bound is sufficient. |
| Lines 2979–2983, anchored square identity | Preserve the explicit factor $E=4s_0$. It is already correct. The new retained-empty-square discussion must use ordinary empty squares $s_0$ consistently; substituting an anchored count directly for $s_0$ would introduce a factor-four error. |
| Lines 3215–3393, three successive counts equal to two | Preserve the statement and the explicit description of the printed proof as an outline with omitted finite branches. Do not upgrade it to a fully displayed classification proof during stylistic revision. |
| Lines 3525–3532, clamped-state census | Clarify the relationship between 49 positive clamped-pair states and checks over $8^3$/$8^4$ encoded words. Seven positive symbols give 49 pairs; eight encoded values presumably include an unused or rejected zero value. Verify that convention in the archived model before adding the explanation. There is no basis here to silently change the recorded enumeration counts. |
| Lines 4228–4375, older diagnostic graphs | Retain the introductory historical label and every saved cycle. “Replacement cycle” is relative to its stated model, not the latest graph in the paper. A short cross-reference to the new refinement section prevents confusion without rewriting historical tables. |
| Lines 4384–4536, explicit witnesses | Preserve all existing data. Add a separate subsection for the three new $012032$ equality witnesses, using the concrete data below. State edge lengths and zero-based window starts explicitly. |
| Lines 4537–4546, verification procedure | Retain the procedure. The three new transition strings use the same procedure, with their specified nonzero initial vertices. Add the corresponding pair-count check if this subsection is updated: counts must be taken against the whole selected path. |
| Lines 4548–4628, history-share catalogue | Preserve all 55 rows, all 69 displayed compatible words, and the offsets. The conversion $s=r-2$ sends the charged centres $s+6,\ldots,s+10$ to $r+4,\ldots,r+8$, as required. Additional count caps at $s+5$ are conditions and need not be among the charged centres. The explanation that caps below six agree with truncated-count tests is necessary. |
| Lines 4675–4689, bibliography | Two archival references use mutable `tree/main` links: `packingarchive` and `newmodelarchive`. Prefer an inspected immutable revision if one is available. This is a reproducibility improvement, not evidence that the referenced results are wrong. |
| Lines 4747–4773 and new bibliography entries | Keep older pinned references describing their archived status. Add separate pinned references for later completed work rather than changing the meaning of those historical snapshots. A current statement about a previously pending batch must cite its current final evidence. Include the new pair theorem/witnesses, endpoint statements with their exact remaining premises, and six-count/retained-empty-square work where used. |

The full source has no duplicate labels or bibliography keys and no unresolved `ref`, `eqref`, `pageref`, or `cite` keys under a direct textual check. This is a source-consistency check, not a rendered-document or remote-link check. The external bibliographic metadata and access dates were not refreshed.

## Existing witness validation

Every transition string was reconstructed using its printed initial vertex, then every unordered pair was tested for distinctness and the equivalence between cube adjacency and consecutive positions. Both displayed complete vertex lists were checked in the same way.

| Printed witness | Edges | Initial vertex | Final vertex | Pair checks |
|---|---:|---:|---:|---:|
| Record witness | 191 | 0 | 118 | 18,336 |
| First distance-three example | 143 | 193 | 189 | 10,296 |
| Second distance-three example | 138 | 77 | 20 | 9,591 |
| Endpoint-maximal example | 93 | 0 | 289 | 4,371 |
| Eight-dimensional seed | 98 | 0 | 78 | 4,851 |
| Singleton-square example | 137 | 145 | 288 | 9,453 |
| First layer path | 96 | 0 | 48 | 4,656 |
| Second layer path | 94 | 0 | 40 | 4,465 |
| Sharp bound-seven example | 140 | 10 | 282 | 9,870 |
| Shorter-context example | 146 | 161 | 191 | 10,731 |
| Endpoint-free bound-eight example | 148 | 90 | 154 | 11,026 |
| First return example | 146 | 13 | 37 | 10,731 |
| Second return example | 143 | 10 | 25 | 10,296 |

All 118,673 pair checks pass. All three printed endpoint-blocker lists pass, including the reversed 93-edge example. The two projected layer paths intersect exactly at zero. Direct absent-corner enumeration reproduces the return counts $(2,3)$ at offsets $(1,3)$ of the first displayed return and $(3,5,5)$ at offsets $(1,4,5)$ of the second. The 175-row historical catalogue and 55-row history catalogue have consecutive row numbers with no missing or repeated row number.

The read-only finite checks here were executed inline and are described explicitly above; this review does not replace the repository's reproducible witness-verification scripts. No new global conclusion follows from these finite checks.

## New sharpness subsection

A suitable statement is: for canonical direction word $012032$, the lower bound $\alpha_{r+2}+\alpha_{r+4}\ge8$ is attained by complete snakes with pairs $(2,6)$, $(3,5)$, and $(4,4)$. Reversal also gives the opposite ordered pairs. There is no claim that these snakes are longest, or that a count tuple from a disconnected local model extends to them.

| Edges | Initial/final vertices | Window start $r$ | Exact five internal counts | Counted pair |
|---:|---|---:|---|---|
| 142 | $66,34$ | 120 | $(10,2,8,6,12)$ | $(2,6)$ |
| 138 | $18,66$ | 114 | $(13,3,12,5,12)$ | $(3,5)$ |
| 144 | $34,66$ | 136 | $(12,4,12,4,13)$ | $(4,4)$ |

In every row the designated window vertices are $(0,1,3,7,6,14,10)$. Counts above six in this table are actual counts, not the graph symbol representing $[6,21]$. The saved Lean statements check the exact two designated counts, the actual snake, the direction word and its canonical form; the complete five-tuples additionally have independent direct finite checks.

The following strings were derived from the saved oriented vertex lists and independently reconstructed. Spaces separate groups only.

142 edges, initial vertex 66:

```text
8023821023 4102182752 1637027815 4308528120 8635830218
0587012034 1057485730 4103784204 5871275263 7081201438
5347180213 7128320814 0120327380 3715812832 08
```

138 edges, initial vertex 18:

```text
8015037241 2517012541 5721680723 0217615720 3143653201
2514380742 3824582374 0120562075 2017487130 7215768210
2362014810 2517012032 5075126810 83025705
```

144 edges, initial vertex 34:

```text
7023807318 3726876417 5671023713 4104605745 2148154163
2037530236 1230810216 0840610235 7302841627 8460280631
8307182713 7081453081 0248203163 8124180120 3263
```

The three new snakes pass 30,184 additional unordered-pair checks and all five counts were independently recomputed against each complete selected set. Adding them would give 16 printed snakes and 148,857 within-path pair checks, before any separate cross-path or blocker checks.

## Evidence and status boundaries

The new witness data are `milestones/121-replacement-window-pressure/data/boundary-paths.json`, SHA256 `5c044ec9fdde3f73cb7d1d2cf008d0033d261f6a25fa59026b09ec5507d33a34`. Its original preparation-stage text still says source-only; the later successful receipts supersede that stage. This review checked the current source, saved source snapshot, compiled object and log hashes for each witness, and read all 24 printed axiom reports. Only `propext` and `Quot.sound` occur in these reports.

| Witness | Successful receipt SHA256 | Source SHA256 |
|---|---|---|
| Pair $(2,6)$ | `b862eaa31b7cea84c1d80e83ea20bea5f6f270daea698aad1a6cf63350f10465` | `166371f14e318347e618b45160b44a0824cf47b7e88aa11c69ffe7730755e91d` |
| Pair $(3,5)$ | `acc33269cf59357b5812dbd71fbfe00dcbcf92269d982ff47fc53e72ed068329` | `f3f96bbf839613a5f833b5c79d6dde1d91e55af1a18bba79dc91e65cc4f8cb68` |
| Pair $(4,4)$ | `17b2d42e7b89d2cbc0bcc806fdb91b331083311262f12c5edac5b472f15c095a` | `9d566450c5706a6b39b13e9b7c189794c99dba0b1fab0946b7d0d3360f15ae28` |

The corresponding successful durations are 39.297, 41.079 and 75.687 seconds. This review did not recompile them or rehash their full inherited dependency closure. The saved complete receipt review is `data/final-receipt-review.json` in that milestone, SHA256 `7011b59330d95202bb52fe245b4c1eae789daa947148facc0a8bb4d96b7eecab`.

Later local exclusions do not erase the historical status of old graph cycles. A cycle excluded by a new rule remains a valid diagnostic of the earlier graph when its model is identified. Likewise, current six-count and empty-square implications retain their universal floor, deficit, or empty-square hypotheses unless independently discharged. The old anchored identity already supplies the correct conversion for expressing those new implications in ordinary empty-square notation. No new unconditional upper bound is established by this appendix review.
