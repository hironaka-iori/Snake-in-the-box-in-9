# Saved seven-cycle review

Result: `PASS_BOUNDED_SAVED_CYCLE_AND_CATALOGUE_REVIEW`. The saved conditional-floor18 cycle contains one exact low-count window of shape \(012301\) with internal counts \((3,3,3,5,2)\) per seven-edge period. Its two appearances in adjacent saved rows describe the same window. The current selected route is to certify an ordinary exclusion of this shorter pattern. The native query has returned `UNSAT_UNCERTIFIED`; this review does not certify its proof.

## Rows and count alignment

Positions are zero-based. For nine directions \(d_0,\ldots,d_8\), the path vertices are \(v_0,\ldots,v_9\). The six saved counts belong to \(v_3,\ldots,v_8\). For a five-count placement \(s=0,1\), the generator takes directions `[s+2:s+8]` and counts `[s:s+5]`. The explicit index formula in the completed milestone72 generator independently confirms this offset. The five-centre share geometry in milestone59 uses vertices four through eight; that separate share-centre list must not be mistaken for the six stored count positions.

In the table, \(6^+\) means the entire interval \([6,21]\). It is never an exact count of six.

| Row | Edge | Nine directions | Six count symbols | Conditional weight | Completed-profile weight on this edge |
| ---: | ---: | --- | --- | ---: | ---: |
| 0 | 2976834 | 012341250 | \((3,3,5,2,6^+,6^+)\) | 736 | 732 |
| 1 | 1008492 | 012301450 | \((3,5,2,6^+,6^+,3)\) | 376 | 376 |
| 2 | 1519107 | 012304530 | \((5,2,6^+,6^+,3,3)\) | 376 | 366 |
| 3 | 4274211 | 012345230 | \((2,6^+,6^+,3,3,3)\) | 376 | 376 |
| 4 | 3053717 | 012341254 | \((6^+,6^+,3,3,3,5)\) | 616 | 616 |
| 5 | 992157 | 012301430 | \((6^+,3,3,3,5,2)\) | 256 | 251 |
| 6 | 1273862 | 012304235 | \((3,3,3,5,2,6^+)\) | 736 | 736 |

The conditional weights sum to \(3472\), with mean \(496\). The same cycle under the completed profile has sum \(3453\) and mean \(3453/7\). The latter is an upper comparison for that profile's minimum, not its minimum: the saved completed profile has a different four-edge cycle of mean \(488\). Neither profile is an unconditional statement about actual snakes. In particular, the conditional profile retains additional share-floor assumptions.

All seven direction words match their indexed entries in the source metadata. Count-code decoding, graph-state closure, canonical eight-direction overlap, and five-count overlap were checked independently. The count sequence has period \((3,3,5,2,6^+,6^+,3)\). No row matches \(012032\) in either five-count placement, and no seven-direction suffix matches the targeted six-count shape \(0123104\), including reversal. Therefore those two earlier strengthening rules do not affect this cycle.

## Shared low-count windows and catalogue comparison

The pattern \(012301/(3,3,3,5,2)\) occurs in row 5 at directions `[3:9]`, with counts at vertices four through eight, and in row 6 at directions `[2:8]`, with counts at vertices three through seven. These are the suffix and prefix views of one consecutive window. The associated exact four-count subwindows are \(01230/(3,3,3,5)\) and \(01230/(3,3,5,2)\). The smaller \(0123/(3,3,3)\) appears in rows 3–6, again as one window viewed at four offsets. These repeated records must not be counted as separate endpoint events.

Every eligible two- through five-count subwindow of all seven rows was compared, with reversal, to the 732-entry milestone39 exclusion catalogue. None matches. The ten completed milestone72 interval exclusions were checked at each permitted placement and orientation, preserving \([6,21]\) for symbol six; none matches. Their membership in the recorded completed cases was also checked.

Nearby catalogue entries require care: \(0120/(3,3,3)\) is excluded, whereas \(0123/(3,3,3)\) is absent from that catalogue. The catalogue also includes \(012301/(3,3,3,3,3)\) and \(012301/(3,3,3,3,4)\). Neither covers the present fourth count five. The completed milestone73 count-free share catalogue supplies weight floors rather than count exclusions. This bounded comparison does not claim an exhaustive search of every historical theorem or external literature.

## Current native result and one future endpoint test

The coordinator's preserved full-row query fixes directions \(012301430\), leaves its first two internal counts unrestricted, and constrains the remaining six to \(([6,21],3,3,3,5,2)\). Its saved status is `UNSAT_UNCERTIFIED`, with no forbidden-endpoint assumptions. A shorter query fixes only directions \(012301\) and upper caps \((3,3,3,5,2)\), with all five lower bounds zero. It likewise has no endpoint restrictions and records `UNSAT_UNCERTIFIED` after cycle exclusions. The corresponding source metadata and run receipts are pinned in the JSON. This audit has not replayed either refutation or certified its semantic premises.

The normalized shorter window is \((0,1,3,7,15,14,12)\). Adding vertex eight yields the induced eight-cycle in cyclic order

\[
0,1,3,7,15,14,12,8,0.
\]

This cycle geometry was checked directly. The claim that the count caps force the extra vertex is not established by this review. Isolating and certifying the necessary cycle exclusion is the coordinator's current work.

The single smaller endpoint candidate retained for future testing is: **a fitting \(0123\) window in an actual induced path in \(Q_9\), with exact three internal counts \((3,3,3)\), forces one actual endpoint to be at distance two from both outer internal centres.** No path-length parity assumption is proposed. For the normalized window \((0,1,3,7,15)\), the two centres are one and seven. Of their fourteen common distance-two vertices, only

\[
4,13,21,37,69,133,261
\]

survive the internal-degree exclusions. Thus a first local test would need four directions, three count conditions and seven negative endpoint units. This candidate is unproved and is not part of the currently selected ordinary-exclusion proof. The longer native contradictions do not imply it.

## Scope

The independent checker reads small saved JSON and source files only. It runs no solver, Lean compiler or full-graph computation, and loads no original graph arrays. Original array-row provenance remains the earlier milestone131/132 audit evidence; the present checks reconstruct the metadata direction lookup, count encoding, overlaps and catalogue matches. Every input and the checker source are hash-pinned in `data/cycle-review.json`. No actual realization of the periodic graph cycle, universal endpoint theorem, novelty claim or global upper bound is established here.
