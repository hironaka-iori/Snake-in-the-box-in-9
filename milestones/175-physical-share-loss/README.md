# Round 175: physical loss integration and stronger boundary counts

The round resumes the saved state at 9e5fe11f. It closes the pending physical share-loss integration and finds a more effective boundary estimate. The full Q9 optimum remains unresolved; there is no newly unconditional numerical length bound.

## Checked results

All accepted modules have successful Lean 4.19 receipts and printed theorem dependencies restricted to propext, Classical.choice, and Quot.sound. The original unexecuted drafts in rounds 172–174 are preserved. Corrected copies and failed attempts are kept here.

1. The physical empty-square and neighbour counts agree with the older share-budget definitions. The sum of selected shares plus physical loss equals 12 times the number of empty square-corner incidences. For a nontrivial snake, G + 840(m+1) + L <= 221136.
2. The actual-snake wrappers of rounds 173–174 pass. Under the older packing and potential premises, m >= 235 implies m = 235 and L <= 3; the snake dominates Q9 and at most three corners have positive loss. These results remain useful, but the new boundary argument below removes the need to establish positive loss for the conditional 234 comparison.
3. Seven consecutive internal singleton counts sum to at least 16. Six sum to at least 14. The prefix versions are checked against actual cube paths using the archived, checked exclusions of adjacent counts (1,3) and three consecutive twos. The reused 152-module source closure matches its saved source manifest; the new theorem axiom reports exclude extra assumptions.
4. The nine-transition share packing improves from W + 2520 <= 5G to W + 2880 <= 5G. Actual singleton truncation, endpoint contributions, selected-vertex share reindexing, and fivefold window capacity are checked together.
5. With the existing potential premise 4462(m-8) <= 9W + 5411, the new packing yields 42262m + 45L <= 9928507. Therefore m <= 234 without any positive-loss premise. The actual-snake conditional theorem retains the local share bounds and the potential premise explicitly. The missing graph interpretation and local certificates are not discharged by this result.
6. For the archived count-only 235 argument, the first six counts and two endpoints now contribute at least 22 instead of 14. Its existing walk premise then gives T >= 4m-13, and the square census gives 39m + 2s0 <= 9192. At m=235 this forces s0 <= 13. Thus 14 empty squares would suffice to exclude 235, improving the previous target of 18. Lean checks the actual boundary and the subsequent implication under the archived walk premise; the full independent rebuild of that contributor argument is still pending.

## Short proof of the new boundary

Every count is positive; a count one has neighbouring internal counts at least four; three consecutive counts cannot all equal two. Any triple has sum at least six, and equality forces (1,4,1). Any four consecutive counts have sum at least nine. For seven counts, split into four and three. If the latter triple sums to at least seven, the total is at least sixteen. If it sums to six, its first count is one, forcing the preceding count to be at least four; the first triple contributes at least six, again giving sixteen. For six counts, split into two triples. If neither has sum six, the result is at least fourteen. If one equals (1,4,1), the adjacent count is at least four and the remaining adjacent pair sums to at least four, giving fourteen.

Both integer minima are sharp for these limited count rules. Arithmetic strings such as (2,2,3,2,2,3,2) attain sixteen. No realizing snake with this boundary is claimed. Independent enumeration records all six seven-term minimizers. An independent audit of all 131 saved 191-edge snakes confirms the inequalities; their observed six- and seven-term minima are 31 and 38, and their two-sided boundary minima are 62 and 71. These observations do not strengthen the universal theorem.

## Verification boundaries and continuation

The native finite graph potential from round 164 remains a separate certificate on a restricted graph. Its local floors, exclusions, count conditions, and graph-to-snake interpretation still need their documented proofs. The share18 replay remains at 33,111 of 145,215 deductions. No new witness longer than 191 was found or searched for in this round.

Next round: use the stronger boundary to weaken the pending share requirements, beginning with a one-unit reduction per edge. Audit the finite graph carefully: changing a floor does not justify restoring excluded transitions or declaring their exclusions proved. Revise the main and short papers together at the scheduled round 176 review, then pause as requested after these two rounds.
