# Milestone 120: a checked restriction on four outer counts

For every six-transition window with canonical directions 012031, at least
one of the first, second, fourth and fifth internal singleton-square counts
is at least 4. The middle count is unrestricted. Lean checks the local
contradiction, its transfer to every actual snake, both graph orientations,
and three new reference-catalogue consequences. There are 26 checked modules
and 11 printed theorem-dependency audits. No new mathematical definition is used.

The original nine-transition target, edge 18806 with word 012031043, is
therefore excluded over its entire recorded count intervals. Weakening that
target exposed the shorter restriction. The selected proof has 5,956 deductions
and 344,241 hints; a separate encoder reconstruction and native replay agree.
Three more reference entries are discharged, taking the checked total to 15
and the remaining total from 1,366 to 1,363.

The graph experiment removes 63 additional transitions, including two edges
of the old conditional cycle. A replacement five-cycle preserves its mean
496 and potential range 602. The other profile retains mean 2915/6 and range
1730/3. Their integer comparisons remain 234 and 235, respectively. These
experiments inherit unresolved count-sum hypotheses and graph assembly work;
the new local theorem does not make either experiment unconditional.

The radius-three model admits a checked disconnected forest with counts
(4,4,13,4,4). The corresponding full-Q9 search remains UNKNOWN after 20 seconds
and 31 retained cycle cuts. Thus sharpness for actual snakes is unresolved.
All 131 saved bank paths pass 2,402,016 pair checks. Their 868 occurrences of
012031 have largest outer count at least 7. No replacement-cycle count tuple
occurs in that bank. These finite observations give no universal strengthening.

At the process-verified snapshot, batch 104 has checked 170/791 completed-profile
contexts and 167/791 conditional-profile contexts; batch 115 has checked
277/1397 modules. Both drivers remain active and unchanged. Their final proofs
are pending. The maintained interval remains 191 through 235 edges, supported
by the contributor proof and archived audit for 235; its complete independent
rebuild remains pending. Conditional 234, the optimum and the value 196 remain
unresolved. Paper revision 116 and both source copies are unchanged; the next
full paper revision is 126.

## Next test

Test full-Q9 realization of edge 2511 from the replacement five-cycle. Its
nine directions are [0,1,2,0,3,1,0,4,1], and its eight internal count bounds are
[[0,21],[0,21],[4,4],[4,4],[3,3],[5,5],[4,4],[4,4]]. The six recorded counts
are at centres 3 through 8. No sum cap, history condition or share condition
is added. The prepared input is `data/next-edge-case.json`; it is untested.

A positive result needs an independent complete-path check. A negative result
needs a saved refutation, an encoding check and Lean replay. Test any viable
restriction on both profiles before claiming numerical progress. Preserve the
live 104 and 115 jobs and the pending 117 and 119 negative certificates.

## Evidence and reproduction

- `mathematical-note.md`: statement, proof route, graph consequences and limits.
- `lean/ActualOuter120.lean`: actual count inequality and oriented graph guards.
- `lean/ReferenceCoverage120.lean`: three new entries and exactly 1,363 remaining.
- `data/native-audit.json`: identical plain encoding and both native replays.
- `data/probe-audit.json`: all 11 probe records, retained cuts and positive geometry.
- `data/graph-audit.json`: independent orientation, removed-key, cycle and arithmetic checks.
- `data/bank-scan.json`: actual bank-path checks and exact count comparisons.
- `audit/final-proof-review.md`: final checked proof scope and receipt audit.
- `audit/attempts.md`: preserved initial dependency-order failure and unselected work.

`scripts/verify_saved.py --verify` checks saved hashes and proof receipts.
The initial ungrouped export, grouped export, failed-order attempt, native
proofs, checked sources, objects and logs are all retained. Reports written
before final compilation preserve their historical pending status; the final
proof review and checkpoint record the completed checks. No new global upper
bound or proof of sharpness is claimed.
