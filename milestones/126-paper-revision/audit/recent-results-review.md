# Recent mathematical results for the paper revision

This review covers milestones 117–125 and the original manuscript passages at lines 325–425 and 2225–2443. It reads the mathematical notes, final proof reviews, relevant theorem sources, saved graph results, and witness records. It does not run a solver, a compiler, or a graph calculation, and does not change any research evidence or manuscript source. Line references below refer to the manuscript before the milestone-126 revision.

## Required changes to the result inventory

The maintained research interval remains 191 to 235 edges, with the existing independent-rebuild limitation on the upper-bound evidence. None of milestones 117–125 proves a smaller unconditional length bound. A length of 196 remains a hypothesis rather than a result of these rounds.

The new closed local results are:

1. For a fitting six-transition word 012031, at least one of the first, second, fourth and fifth internal singleton-square counts is at least four. The middle count is unrestricted apart from its general upper bound 21.
2. For a fitting six-transition word 012032, the second and fourth counts are each at least two and their sum is at least eight. All three equality types, up to reversal, occur on checked complete snakes.
3. For a fitting seven-transition word 0123041, in either orientation, the six internal counts sum to at least 25. This is one direction class, not a universal six-count theorem.
4. For a fitting seven-transition word 0120324 whose six internal counts sum to at most 22, the second count is at least two and the fourth is at least three. The resulting six intervals are \([1,21],[2,21],[1,21],[3,21],[1,21],[1,21]\). This restriction does not rule out such a window.
5. Keeping ordinary empty squares in the incidence bound gives a checked necessary deficit inequality for every sufficiently long actual snake. The resulting bounds of 234 and 233 require explicit additional count or empty-square hypotheses.

The catalogue count must change from twelve to twenty discharged entries, and from 1366 to 1358 outstanding entries. The final graph family uses thirteen five-count sum rules, with several rules still unproved. The word “completed” in “completed-share profile” describes the share component; it does not make these newer sum-rule graphs unconditional snake bounds.

## Claim status by milestone

| Milestone | Mathematical content | Current supported status |
| --- | --- | --- |
| 117 | On 012034, middle count at most 5 implies the sum of the other four counts is at least 16. | Native contradiction replay and conditional geometric transfer checked. The concrete semantic composition and full Lean contradiction remain pending. Keep the actual-snake inequality conditional. |
| 117 | Eleven-rule graph has means \(2915/6\) and \(496\). | Exact finite-graph calculations with full edge inequalities and attaining cycles. Inherited sum premises and global assembly remain separate. |
| 118 | A universal 012301 outer sum of at least 13, including when the middle count is at least 6. | Refuted in the radius-four relaxation by disconnected forests, including outer sums 11 and 12. These are not counterexamples among complete snakes. |
| 118 | A 012301 total of at least 19, or at least 20 when the middle count is at least 6. | Also contradicted by local forests only. Smaller proposed floors 18 and conditional 19 remain unresolved. Concrete path-component and count data passed Lean; radius and boundary conditions were independently checked outside Lean. |
| 119 | A universal 012304 five-count total of at least 23, even under bounds \((\le4,\ge6,\le4,\le4,\ge6)\). | False for actual snakes. A checked 148-edge induced path has counts \((3,6,3,4,6)\), total 22. |
| 119 | On 012304, \((\alpha_1,\alpha_3,\alpha_4)=(2,2,3)\) and \(\alpha_2,\alpha_5\ge6\) imply \(\alpha_2+\alpha_5\ge16\); the corresponding triple \((2,4,2)\) implies pair sum at least 15. | Native certificate evidence only; these are the twelfth and thirteenth proposed sum rules. Both would give total at least 23 on their narrower classes. |
| 120 | The four outer counts of 012031 cannot all be at most 3. | Closed actual-snake theorem, including concrete local semantics, contradiction and canonical transfer. Three reference entries discharged. |
| 121 | The second and fourth counts of 012032 are at least 2 and sum to at least 8. | Closed, sharp actual-snake theorem. Five further reference entries discharged. |
| 122 | Equality pair \((2,6)\) on 012032 places both endpoints at distance two from both counted vertices. | Closed actual-snake theorem in the frozen review; reversal gives \((6,2)\). The counts are actual counts, not clipped symbols. |
| 122 | All equality cases on 012032 have that endpoint property; therefore there are at most 13 equality windows. | The assembly and counting implications are checked, with the remaining endpoint cases explicit. The frozen complete review closes only \((2,6)\). The later \((3,5)\) replay now has successful local receipts, while the final \((4,4)\) and actual assembly are pending at the live observation below. Publication may safely use the frozen status. |
| 123 | Six internal counts on 0123042 sum to at least 26. | Native negative evidence, no completed contradiction certificate. Keep as a hypothesis. |
| 123 | Exact six-fours case 10 is impossible. | Concrete formula and satisfaction semantics checked; remaining contradiction modules pending. Do not add it to the completed exclusion count. |
| 123 | Six-window and guarded five-window excess accounting. | Generic coefficient-20 and guarded coefficient-24 inequalities passed Lean. They preserve explicit local floor hypotheses and do not establish graph realization or global assembly. |
| 124 | Six-count total at least 25 on 0123041, in either orientation. | Closed actual-snake theorem. The final review covers 46 modules and 22 printed reports, including the direct conditional length statements. |
| 124 | Universal six-count floors 25 and 26 imply lengths at most 234 and 233. | Closed actual-snake implications, with their universal floors unproved. A 39-block total deficit at most 28 also implies length at most 234. |
| 124 | If every one of those blocks has sum at least 23 and at most fourteen have sum below 25, the deficit is at most 28. | Checked arithmetic implication. The local floor and exception-frequency assumptions remain unproved. Thirteen exceptions give the stronger deficit bound 26. |
| 125 | Retained empty-square budget and necessary deficit bound for lengths at least 235. | Closed actual-snake statements. The ordinary-square interpretation uses four anchored incidences per square. |
| 125 | Floor 24 plus at least six ordinary empty squares, or floor 23 plus at least twenty-five, gives length at most 234. Floor 25 plus at least fourteen empty squares gives at most 233. | Checked actual-snake implications with explicit hypotheses. None of the new universal floors or empty-square lower bounds is proved. |
| 125 | A 0120324 window with six-count total at most 22 must satisfy the six reduced intervals above. | Closed actual-snake theorem after the preserved source repair. This is the successful final status; the frozen search audit records the earlier, unsuccessful compilation stage. |
| 125 | Floors 23 or 25 on 0120324. | Unresolved. All three saved native attempts timed out. No completed contradiction or counterexample was obtained. |

The generic lower bound 18 for six variables in milestone 125 is an arithmetic consequence of its displayed inequalities. Its proof does not instantiate every premise for a snake. In particular, a source comment about a consecutive triple does not discharge its actual-window premise. Do not advertise it as a new universal snake theorem.

## Exact catalogue count and sharp witnesses

The source `milestones/121-replacement-window-pressure/lean/ReferenceCoverage121.lean` explicitly proves refutation of twenty distinct reference entries, the equivalence with the filtered remainder, the remaining length 1358, and the five new index equalities. Its current SHA256 matches its successful receipt:

`3d60dbf4867f1fedae1016f605b8cefaa6907b84b075ee515b74ef132147ea8a`.

The three milestone-120 additions are indices 126, 127 and 138 on 012031, with count symbols \((2,3,6,3,2)\), \((2,3,6,3,3)\), and \((3,3,6,3,2)\). The five milestone-121 additions are indices 196–200 on 012032, with symbols

\[
(2,2,6,5,2),\ (2,2,6,5,3),\ (2,3,6,3,2),\
(2,3,6,3,3),\ (2,3,6,3,4).
\]

In each entry, symbol 6 retains the entire interval \([6,21]\). The additions are direct interval containments, with no exact-six substitution. The remaining 1358 entries are still an obligation.

The complete sharpness paths are saved in `milestones/121-replacement-window-pressure/data/boundary-paths.json`, SHA256 `5c044ec9fdde3f73cb7d1d2cf008d0033d261f6a25fa59026b09ec5507d33a34`. That file includes each complete ordered vertex list. Their checked source arrays are in `lean/Boundary26.lean`, `lean/Boundary35.lean`, and `lean/Boundary44.lean` within the same milestone. All three current source hashes match successful receipts.

| Edges | Window start | Exact five counts | Second/fourth pair | Ordered endpoints |
| ---: | ---: | --- | --- | --- |
| 142 | 120 | \((10,2,8,6,12)\) | \((2,6)\) | \((66,34)\) |
| 138 | 114 | \((13,3,12,5,12)\) | \((3,5)\) | \((18,66)\) |
| 144 | 136 | \((12,4,12,4,13)\) | \((4,4)\) | \((34,66)\) |

The designated window is \((0,1,3,7,6,14,10)\) in all three orders. These are complete induced paths, independently checked at all 30,184 unordered pairs and subsequently checked in Lean. The bound eight and the separate minimum two are sharp. These paths do not improve the global lower bound.

## Proposed mathematical text

The following passages use ordinary mathematical notation and can be adapted into the manuscript without source filenames.

### The six-transition pair bound

**Theorem.** Let \(P=(x_0,\ldots,x_m)\) be a snake, and suppose that its six transitions starting at \(x_r\), with \(r+6\le m\), are \((a,b,c,a,d,c)\), where the four named coordinates are distinct. Then

\[
\alpha_{r+2}\ge2,\qquad \alpha_{r+4}\ge2,\qquad
\alpha_{r+2}+\alpha_{r+4}\ge8.
\]

All three constants are best possible.

**Proof.** Translate the first vertex to zero and rename the four coordinates. The normalized vertices are \((0,1,3,7,6,14,10)\). Three checked local contradictions exclude the respective count caps \((1,21)\), \((2,5)\), and \((3,4)\) on the second and fourth centres; the other three counts remain unrestricted within \([0,21]\). These contradictions use the necessary local conditions for an actual snake. Reversing the path gives the corresponding exclusions with the two counted positions exchanged, since reversal preserves the canonical direction pattern. The first exclusion gives both minima. If the sum were at most seven, one count would be two with the other at most five, or one would be three with the other at most four. Each possibility is excluded. The complete snakes with pairs \((2,6)\), \((3,5)\), and \((4,4)\) attain equality; reversing the first also attains two in the other position.

This theorem concerns positions \(r+2,r+4\) in a six-transition pattern. It must remain separate from the existing eight-transition theorem at manuscript lines 325–425, which concerns positions \(r+2,r+6\), has sharp sum seven, and has its own nineteen-vertex endpoint demand set.

### The checked six-count direction class

**Theorem.** Suppose that seven consecutive transitions of a snake, in either orientation, become \((0,1,2,3,0,4,1)\) after coordinate renaming. If the first vertex of the window has index \(r\), then

\[
\sum_{j=1}^{6}\alpha_{r+j}\ge25.
\]

**Proof.** Normalize the window to \((0,1,3,7,15,14,30,28)\). Each of its six internal vertices contributes the 21 opposite corners whose directions avoid its two prescribed path edges. Concatenating these lists gives 126 occurrences and 105 distinct vertices. Repetitions retain their multiplicity because a corner can contribute to more than one count. If the displayed sum were at most 24, the selected vertices and actual endpoints of the snake would satisfy the necessary full-cube conditions and the joint count constraint. The retained contradictory input has 3649 clauses; its checked refutation uses 5746 deductions and 439766 antecedent references. The finite input interpretation and refutation have passed Lean, so the assumed sum is impossible. Reversing the snake reverses the six internal counts and preserves their sum.

The last sentence is justified by the checked reverse-snake argument. The result does not assert sharpness of 25 or a floor for any other direction class. The full input had 101898 clauses on 5072 variables and used no cycle cuts; those details are appropriate for the certificate appendix if space is limited in the main proof.

### Necessary restrictions on the unresolved direction class

**Proposition.** Suppose that \(r+7\le m\), the seven-transition word is \(0120324\), and

\[
\sum_{j=1}^{6}\alpha_{r+j}\le22.
\]

Then \(\alpha_{r+2}\ge2\) and \(\alpha_{r+4}\ge3\).

**Proof.** The prefix has word \(012032\), so both counts are at least two. Suppose that the fourth count is two. The existing exclusion of a first count at most two together with a fourth count at most three forces \(\alpha_{r+1}\ge3\). The suffix beginning at \(x_{r+1}\) has canonical word \(012314\). Its middle count is \(\alpha_{r+4}=2\), so the proved outer-sum inequality gives

\[
\alpha_{r+2}+\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\ge19.
\]

The six counts would therefore sum to at least \(3+2+19=24\), a contradiction. Internal positivity and the general bound 21 supply the other four intervals.

This proposition leaves the interval system feasible as a research question. It proves neither a floor of 23 nor a floor of 25 on this pattern.

### Six-count blocks with the empty-square term retained

For a nontrivial snake, the endpoint counts are at least four, each internal count is positive, and

\[
T+35(m+1)+2s_0\le9214,
\]

where \(s_0\) is the number of ordinary empty squares. If \(m\ge235\), group the internal positions 1 through 234 into 39 disjoint blocks of six. Their total shortfall below 25 is

\[
D=\sum_{b=0}^{38}\max\left(0,25-\sum_{j=1}^{6}\alpha_{6b+j}\right).
\]

The blocks contribute at least \(975-D\). The remaining \(m-235\) internal vertices contribute at least one each, and the endpoints contribute at least eight. Hence

\[
T+D\ge m+748.
\]

Combining this with the retained incidence bound gives \(D\ge29+2s_0\) for every snake of length at least 235. Consequently, proving \(D\le28+2s_0\) for every candidate of that length would prove \(m\le234\).

The symbol \(D\) is useful here because it is used throughout the argument and in the remaining target. No additional named objects are needed. The implementation uses natural subtraction, which corresponds to the displayed nonnegative part. Using ordinary integer subtraction without the maximum would change the statement.

The checked alternatives are:

| Hypotheses on all six consecutive internal counts and on sufficiently long snakes | Conclusion |
| --- | --- |
| Every such sum is at least 25. | \(m\le234\). |
| Every such sum is at least 26. | \(m\le233\). |
| Every such sum is at least 24, and \(m\ge235\) implies \(s_0\ge6\). | \(m\le234\). |
| Every such sum is at least 23, and \(m\ge235\) implies \(s_0\ge25\). | \(m\le234\). |
| Every such sum is at least 25, and \(m\ge234\) implies \(s_0\ge14\). | \(m\le233\). |

For the first two statements, 38 disjoint blocks and the remaining positive internal counts give \(T\ge m+38L-221\), where \(L\) is 25 or 26. The respective forbidden lengths 235 and 234 contradict the incidence budget. For the next two statements, 39 blocks give \(T\ge m+709\) and \(T\ge m+670\). At \(m=235\), their retained charges are at least 9216 and 9215, respectively. For the final statement, 38 blocks give \(T\ge m+729\); at \(m\ge234\), the incidence budget forces \(s_0\le13\). All universal sum and empty-square lower-bound premises remain open.

The anchored implementation counts each ordinary square four times. Its inequality is \(4T+140(m+1)+2A\le36856\) with \(A=4s_0\). Dividing gives the stated coefficient \(2s_0\); substituting \(2A\) into that divided formula would be incorrect.

## Safe endpoint text and current batch observation

Safe publication wording based on the frozen review is: “For actual equality pair \((2,6)\), and by reversal \((6,2)\), both endpoints are at distance two from both counted vertices. Extending this conclusion to the equality types \((3,5)\), \((5,3)\), and \((4,4)\) remains part of the certificate completion. If the conclusion holds for every equality window, at most thirteen such windows can occur.”

The count thirteen has a short independent explanation. Each first counted vertex lies in the intersection of the distance-two spheres about the two endpoints, which has at most fourteen vertices. Distinct starts give distinct first counted vertices. For a nonempty set of starts, the second counted vertex of the last window is additional to all those first vertices. Thus the number of starts plus one is at most fourteen. This argument assumes the endpoint property at both counted centres and both endpoints; a demand for only one endpoint is insufficient.

For an equality credit \(C\ge0\), the corrected comparison uses the conditional occurrence budget thirteen:

\[
(4200d+p)m\le1098960d+13Cd+8p+R.
\]

The older endpoint graph experiment used fourteen; its saved output must retain that historical value. It is possible to state the sharper arithmetic separately, without silently rewriting the saved experiment.

At approximately 2026-11-03 05:55–05:56 UTC, the pending 381-module plan had 258 successful receipt files through the fourth-case data module 90. The local \((3,5)\) wrapper had a successful receipt, with source hash `b5471cf4ed2bf7b63fb245b8180bd978c8872127043ca119f728e4ca79796d82`; its proof combines the checked local semantics and contradiction. The final \((4,4)\) wrapper and complete actual equality wrapper had no receipt. Live process inspection found launcher PID 55040, child checker PID 16800, and Lean PID 51096 compiling the fourth-case data module 91. This is a time-specific process-backed observation, outside the frozen 67-module receipt review. No batch was changed. The manuscript need not incorporate these evolving receipts.

## Exact finite-graph updates

All rows below are conditional finite-graph evidence. Each has 1601856 states. The older base graph and its separately checked context rows must keep their original counts; these refinements do not replace the base graph definition.

| Saved refinement | Retained edges | Completed-share mean | Completed-share range | Conditional-share mean | Conditional-share range |
| --- | ---: | ---: | ---: | ---: | ---: |
| 117: eleven sum rules | 4697823 | \(2915/6\) | \(1730/3\) | 496 | 602 |
| 119: thirteen sum rules | 4697823 | \(2915/6\) | \(1730/3\) | 496 | 602 |
| 120: add the proved 012031 exclusion | 4697760 | \(2915/6\) | \(1730/3\) | 496 | 602 |
| 121: add the proved 012032 pair exclusions | 4683114 | \(2915/6\) | \(1730/3\) | 496 | 602 |
| 124: add guarded six-count floors \((26,25,25)\) on \((0123042,0120310,0123024)\) | 4673032 | \(2915/6\) | \(1730/3\) | 496 | 602 |

In every row the exact comparisons are \(1324108/5623\) and \(551765/2348\), yielding integer comparisons 235 and 234. The last row reused feasible potentials; it did not prove those ranges minimal. Its producer reproduced both full milestone-121 weight hashes, retained all thirteen sum rules, deleted 10082 new keys, increased 41762 retained credits, and checked every retained-edge inequality in both profiles. Credits use the maximum of the old and new alternatives, not their sum. The first chronological clipped count must be below six; symbol six always denotes \([6,21]\). Deletion requires all six symbols to be exact and their sum below the proposed floor.

The eighteen-cycle and four-cycle saved in milestone 121 survive the final three-shape experiment and avoid all three new shapes. Stronger floors on just those shapes therefore leave the same attaining cycles and exact means. Even a potential range of zero gives comparisons

\[
1323416/5623>235,\qquad 137866/587>234.
\]

The four-cycle's six-direction suffix classes, identified with reversal, are all 0120324. Its chronological tuples are \((5,5,3,3,5,5)\), \((5,3,3,5,5,3)\), \((3,3,5,5,3,3)\), and \((3,5,5,3,3,5)\), with sums 26, 24, 22 and 24. A proved floor 23 would delete the sum-22 edge, index 2219941; a floor 25 would also delete the sum-24 edges. This explains the current target. It does not establish that these cycle contexts are realizable by one snake, or that deleting this cycle improves the full minimum mean.

The completed eighteen-cycle instead uses 0120340, 0120342, 0123014 and 0123104. Its low-sum keys include symbol six. Their exact count sums must not be identified with their clipped sums. A useful floor could contribute excess credit while leaving the full interval key present.

The exact original result files read for this table are:

- `milestones/117-cycle-sum-refinement/data/middle5-outer16/results.json`.
- `milestones/119-shared-five-count-pressure/data/full-critical23/results.json`.
- `milestones/120-nine-transition-window/data/outer3/results.json`.
- `milestones/121-replacement-window-pressure/data/pair-graph/results.json`.
- `milestones/124-six-count-cycle-pressure/data/graph-26-25-25/results.json`, current SHA256 `d3b3c248c4fd14491d444413f18e9a8b5768f12849945ded16afcc44412d9f1a`.

The last experiment's saved-cycle audit is pinned by `e99c16531c6cfa8fda28a187cc75dca6ce5e5c26aef45a28d806a83a91623cfd`, and its direction/count target record by `9d5bf150fca0903496cd1a4e1b55d37457176699477f634b242c500d3adf00c4`. The native evidence on the three floors has different statuses: 0123042 cap 25 returned negative without a completed certificate, 0123024 cap 24 returned negative without a completed certificate, and 0120310 cap 24 remained unknown. All three floors must remain explicit assumptions.

## Exact manuscript update map

- Lines 325–425: retain the eight-transition theorem, its sharp 140-edge witness, the necessity of its outer transitions, and its nineteen-vertex demand set. Add a separate six-transition result rather than replacing its seven by eight or changing its counted offsets.
- Lines 2233–2257: the displayed ten-rule table is now a historical stage. Add the 117 rule and the two narrow 119 rules if describing the final family. Preserve the proved status of the 012314 middle-at-most-two outer-sum theorem and the pending statuses of the other rows. The live 115 batch is outside this review.
- Lines 2287–2337: retain older numerical stages as historical rows or replace the stated final profile by the exact table above. The current attaining cycles have lengths eighteen and four; the older twenty-six/six cycles are not the final family. The current completed comparison is \(1324108/5623\), not \(4781536/20303\).
- Lines 2337–2358: the threshold inequalities remain valid. If using the latest completed slope \(p/d=2915/6\), its zero-range obstruction margin is \(111960\cdot6-227\cdot2915=10055\). The conditional margin remains \(116160-226\cdot496=4064\).
- Lines 2364–2369: replace twelve/1366 by twenty/1358 and cite the final 120 and 121 catalogue checks. Do not describe the remainder as proved.
- Lines 2370–2375: preserve the distinct base-graph context and accepted-key figures unless their own batch review changes them; the refined edge counts above do not replace those baseline figures.
- Lines 2376–2390: keep the stated conditional share hypotheses explicit. The new six-count implications offer an additional route to 234 or 233; they do not discharge those share hypotheses.
- Lines 2391–2428: revise the current fixed-family obstruction and next target using the surviving cycles above. The exact six-fours case10 semantic check does not increase the number of completed exclusions. Do not generalize disconnected local witnesses into actual-snake counterexamples.
- Lines 2429–2443: the recent rounds do not complete the singleton-density-to-snake bridge. Preserve its existing limitation.

## Source verification and final limitations

The final proof reviews read include 117 and 118 `audit/final-review.md`, 119 `audit/full-witness-review.md`, 120 and 121 `audit/final-proof-review.md`, 122 and 123 `audit/proof-review.md`, 124 `audit/proof-review.md`, and 125 `audit/proof-review.md` plus `audit/proof-supplement.md`. Historical source-only reviews were interpreted in conjunction with their later successful receipts.

Original sources were inspected for the actual pair minimum/sum and reverse-path argument, the twenty-entry catalogue list and filter, the six-count forward/reverse theorem, the actual uniform-count implications, the retained empty-square accounting, the two additional empty-square tradeoffs, and the repaired actual 0120324 restrictions. The current source hashes of eleven key modules were compared directly with successful receipts: all matched, with exit code zero and no timeout. This read-only source check supplements the earlier complete receipt audits; it does not rerun their dependency audits.

Key current source pins are:

| Source statement | SHA256 |
| --- | --- |
| Actual pair theorem | `17732a533cc39f73a1d140a69e5b666260a0fdc3ae5731611ff15b5f45090280` |
| Actual 0123041 six-count theorem | `41e077d08093f8b730e7b5d1e61253079f77aeee34302ef9606b303e6f27965a` |
| Its reversal theorem | `b1b09754d64c0e2c136037606198711596bb3cacb828a06a2d231fa20de5c783` |
| Actual uniform-count implications | `48c903830b6af9a660f98dc2b30253b1ad47804d1319cbc0247cb677e73b1869` |
| Retained empty-square and deficit statements | `ae32ad25578a5b34de9194d205b5ff5f13abe1ba7fc86ebaa3dc186e784bf38a` |
| Additional empty-square tradeoffs | `9a6ad77bf1f402b6a6b6ed1765574b7e0df5733a4739c4cf71f13b04d509cb38` |
| Repaired actual 0120324 restrictions | `dbb9f2fbe1ea322903091a73eb3ed36cd677f80a6309cf5aee851a916654ab7a` |

The main remaining tasks are mathematical: extend the single proved six-count direction class, prove a sufficient deficit or empty-square estimate, or close the pending local and graph-to-snake premises. Native timeouts give no negative conclusion, and a numerical graph comparison is not a theorem about all snakes until its local hypotheses and global interpretation are supplied.
