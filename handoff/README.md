# Research update: milestone 124

Lean proves that the six internal singleton-square counts sum to at least 25
for direction pattern 0123041 in either orientation, in an actual snake.
This closes one of the 21 reversal classes. There are 46 checked modules and
22 printed dependency reports in the round.

The universal six-count floor 25 would give length at most 234; floor 26 would
give at most 233. Lean checks these implications for actual snakes. It also
checks a weaker sufficient condition for 234: total shortfall below 25 is at
most 28 across 39 disjoint six-count groups. These additional assumptions remain
unproved. The existing notation is sufficient; no new definition is introduced.

The full-cube screen gives 19 negative classes, including the checked class.
The other 18 need checked contradiction proofs. Classes 0120310 and 0120324
remain unresolved. The three-pattern graph experiment cannot improve the
235/234 integer comparisons because attaining cycles avoid all three patterns.
The maintained range remains 191–235 with its documented independent-rebuild
limitation. Neither the optimum nor 196 is established.

See [the mathematical note](../milestones/124-six-count-cycle-pressure/MATHEMATICAL_NOTE.md),
[proof review](../milestones/124-six-count-cycle-pressure/audit/proof-review.md), and
[coverage review](../milestones/124-six-count-cycle-pressure/audit/coverage-review.md).
Paper revision 116 is unchanged; the next full revision is 126.
The next priority is resolving 0120310 and 0120324 or proving the stated
39-group shortfall bound. The older 104, 115 and 122 batches remain separate.

## Earlier record

# Research update: milestone 123

The six-count work gives checked overlap accounting and a new unproved candidate:
the six internal counts sum to at least 26 on the seven-direction pattern
0123042. Two negative full-cube searches support it; no contradiction certificate
or actual-snake transfer has been completed for this candidate.

Neither the recovered exact-six-fours exclusion nor the tested sum credits
improve the integer comparisons. Replacement cycles avoid 0123042 entirely.
The next focused targets are 0120310 and 0123024, with recorded six-count sum 24.
The maintained interval remains 191–235, with its existing independent-rebuild
limitation; 234 remains conditional. No new mathematical definitions were added.

See [mathematical note](../milestones/123-six-count-recovery/MATHEMATICAL_NOTE.md),
[proof review](../milestones/123-six-count-recovery/audit/proof-review.md), and
[graph obstruction](../milestones/123-six-count-recovery/audit/six-sum-guarded-review.md).
Paper revision 116 is unchanged; the next full revision is 126.

## Earlier record

# Research update: milestone 122

The arbitrary-snake endpoint restriction for the 012032 count pair (2,6) is
Lean checked. The conditional equality assembly and geometric occurrence limit
13 are checked; the (3,5)/(4,4) certificates and unconditional equality conclusion
remain in a 381-module batch. The endpoint credit cannot improve the current
integer comparisons: an all-four three-cycle survives even deletion of every
eligible equality event. The maintained interval remains 191–235, with the existing
independent-rebuild limitation; conditional 234 remains unresolved.

See [mathematical note](../milestones/122-endpoint-equality/MATHEMATICAL_NOTE.md),
[proof review](../milestones/122-endpoint-equality/audit/proof-review.md), and
[graph review](../milestones/122-endpoint-equality/audit/endpoint-graph-review.md).
The next numerical target is the three all-four keys in
`milestones/122-endpoint-equality/data/next-six-four-cases.json`; inspect existing
seven-count coverage before searching. Paper revision 116 is unchanged; revise at 126.

## Earlier record

# Research handover

Read [current status](CURRENT_STATUS.md), [next steps](NEXT_AGENT_PROMPT.md),
and [milestone 121](../milestones/121-replacement-window-pressure/README.md).

For every 012032 window, the second and fourth internal singleton-square counts
are each at least 2 and sum to at least 8. Lean checks the three local refutations,
actual-snake interpretation, reversal and resulting inequalities. Complete
snakes of 142, 138 and 144 edges attain the respective pairs (2,6), (3,5) and (4,4);
their paths, directions and pair counts also pass Lean. The pair bound is sharp
for actual snakes. No new mathematical definition is introduced.

Five further reference cases are discharged. Twenty entries are now checked,
and the exact remaining obligation has 1358 entries. The final proof checks cover
40 modules and 47 printed axiom reports, including the three boundary witnesses
and a separate conditional charge inequality. Standard foundations only occur
in the reported dependencies.

The pair restriction removes 14,646 additional graph transitions, including two
edges of the former conditional cycle. A replacement four-cycle keeps mean 496,
range 602 and integer comparison 234. The other profile retains its eighteen-cycle,
mean 2915/6, range 1730/3 and comparison 235. Both graph experiments retain inherited
unproved sum hypotheses and global assembly work. The local theorem and sharp
witnesses establish no improved global upper bound.

All three sharp witnesses place both endpoints at distance two from both counted
vertices. Three full-Q9 tests demanding an endpoint outside that intersection
return native UNSAT without cycle cuts. Their encodings have been audited, but
the refutations and actual-snake endpoint interpretation remain unchecked.
The proposed endpoint-necessity theorem is therefore a hypothesis.

If proved, it would limit equality to fourteen windows in any snake and rule
out equality in odd-length snakes. Those deductions have written arguments and
a finite sphere-intersection check; their general Lean proofs remain pending.
Lean already checks the conditional arithmetic with the 14C correction. This
does not supply its missing geometric or occurrence-count hypotheses.

The maintained interval remains 191 through 235 edges, with the contributor proof
and archived audit for 235 and its complete independent rebuild pending.
Conditional 234, the optimum and 196 remain unresolved. Paper revision 116 is
unchanged; the next full manuscript revision is 126. The two pre-existing proof
batches remain active; their exact process observations are in the checkpoint.

Certify the three saved endpoint contradictions for boundary pairs (2,6), (3,5)
and (4,4). Each formula is the ordinary full-Q9 window encoding plus one clause
requiring an endpoint outside the intersection of the two exact distance-two
spheres. Rebuild and replay the saved negative cases before proving that extra
clause sound under an actual counterexample. The existing actual pair theorem
and reversal then reduce the equality case to these three inputs.

Prove the resulting occurrence limit 14 and its odd-length consequence. Evaluate
an endpoint credit on both graph profiles with the full 14C budget correction.
Initially award it only to exact pairs (3,5), (4,4), (5,3): clipped symbols (2,6)
or (6,2) may have actual sum greater than 8. The surviving completed-profile cycle
has no 012032 window, so this credit alone cannot improve its cycle mean. Keep
that limitation explicit when deciding the next numerical experiment.

Do not rerun the same bounded probes merely to obtain another negative status.
Their exact inputs and encoding audit are saved in `data/next-endpoint-task.json`.
Preserve the active 104 and 115 batches and the pending 117/119 certificates.
