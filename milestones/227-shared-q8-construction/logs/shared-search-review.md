# Round 227 shared-search source review

## Scope and conclusion

Read all of `scripts/shared_paths.py` (143 lines), `scripts/prepare_companions.py` (45 lines), and `scripts/run_shared.py` (58 lines). Parsed all of `data/companions.json`, compared its configuration domains and geometry with the pinned `regions44.json` and `shared-q8-plan.json`, and inspected the terminal shared120 result and execution receipt. This was source review and small finite data inspection. No worker, solver, compiler, or software test was run by this reviewer.

The mathematical configuration reduction and pruning preserve every compatible pair in the stated seven-context family. One checkpoint correctness defect was found in the reviewed worker: an asynchronous `KeyboardInterrupt` can save a state after removing pending work and before installing its successors. Such an `INTERRUPTED` checkpoint must not support resumed exhaustion. The defect was reported immediately and acknowledged by the parent. The observed shared120 termination is an ordinary `TIME_LIMIT`, for which the reviewed loop saves a complete pending frontier.

## Pinned inputs and sources

| File | SHA256 |
|---|---|
| `scripts/shared_paths.py` | `600a825e5732d28d5592b10cfa561c1ecf7a5e34da009ad6b90ecd3bcd17d4f9` |
| `scripts/prepare_companions.py` | `2e556e4d76563ae01af397f96f53daa66bd810e1197070cec887cb2912618ff0` |
| `scripts/run_shared.py` | `3b8bcf9f4d011a971bd6a12df06dd437f31222f51786ed015c66bd73c0ebedc2` |
| `data/companions.json` | `301a7bc1fd4aac979d86729d9ecde695be39a808b9dbb6617a3e33390eade8dd` |
| `data/regions44.json` | `c2c5b1465726c4e8c2ab142a1524e171cfeb992cb66d906475e9d1e2e766ec0b` |
| `data/shared-q8-plan.json` | `38b68481c0db19dee53410ac64ba25601e7d44bc35110e267e1b81f781c45eda` |

All three pins stored in companions.json match their actual files. The seven saved context rows equal their corresponding source rows, including intervals and allowed domains.

## Configuration coverage

The scope is contexts 194, 195, 196, 197, 198, 199 and 201, with the previously established first upper suffix `[480]`, first lower endpoints 18 and 224, first lower length 43, and exactly two crossings in the second replacement. Establishing these restrictions and the original allowed domains remains a dependency on the earlier geometric and native audits; this review does not independently replace those results.

For an actual second path with two crossings, its upper vertices form an initial portion from its first anchor and a terminal portion to its second anchor. Every such portion is an induced path in the appropriate upper domain. The enumeration visits every induced upper prefix without repeating a vertex, entering the other endpoint, or adding a chord. It records every prefix ending at a vertical port and continues beyond ports, so an earlier port does not prevent a later valid crossing. Pair rejection for equality or adjacency between the two upper portions is necessary: their intervening route contains both crossings and a positive lower segment.

Inspection of the literal upper adjacency lists gives one possible initial portion in each context. The first six terminal upper graphs are trees with two port choices. Context 201 has six induced terminal portions, exactly the six stored configurations 12 through 17. Thus the saved total is 18 configurations, distributed as two in each of the first six contexts and six in context 201.

For every configuration, independently reconstructed upper projections, lower anchors, lower edge count, intervals, first domain and second lower domain agree with the saved lists. Removing the closed neighbourhood of vertex 480 is necessary because that vertex belongs to the other replacement. An upper vertex can contact a lower vertex only at its vertical projection. The second lower domain therefore removes all upper projections except its two required ports; the first lower domain removes all these projections. The second lower length is \(44-|A|-|B|\), where \(A\) and \(B\) are the upper vertex sequences. This yields exactly 45 vertices in the assembled second replacement.

The literal equal-task groups are `[0,2,4,6,8,10,12]`, `[1,3,5,7,9,11,13]`, `[14]`, `[15]`, `[16]`, and `[17]`. The first two groups have equal lower anchors, lengths and domains; replacing the two lower paths by symbolic placeholders also gives identical complete 193-vertex sequence templates within each group. This reduction requires no assumed symmetry.

Configuration 17 has the same lower anchors `[35,201]` and lower length 33 as configuration 0. Its first and second domains are exactly those of configuration 0 with vertex 212 removed. Consequently every pair admitted by 17 is admitted by 0. Removing the same mandatory-anchor neighbourhoods preserves this inclusion. The five representatives `[0,1,14,15,16]` therefore suffice for an absence result in this family.

## Common-prefix traversal and pruning

For each representative, excluding the closed neighbourhoods of the other path's two anchors is necessary for disjoint, nonadjacent replacement paths. After these deletions, the first/second domain sizes are respectively 99/99, 98/99, 98/99, 98/98 and 97/97 for representatives 0, 1, 14, 15 and 16. Their second lower lengths are 33, 32, 39, 38 and 35.

At a first prefix, an option survives only if all prefix vertices belong to its first domain and its second domain, after deleting the closed neighbourhood of that prefix, still has enough connected vertices of both colours to support the required second path. These are necessary conditions. Additional first vertices only remove second candidates, so a discarded option cannot become feasible below that prefix.

The first extension uses the union of the surviving first domains. A valid completion for any surviving representative lies in that union. Vertices admitted only by another representative can create extra work, but the next option filtering removes incompatible representatives. A prefix is rejected altogether only when all options fail or when the union itself cannot support the required first continuation. Thus sharing prefixes implements the required disjunction.

The extension routine lists every unused adjacent vertex in the remaining component. Deleting closed neighbourhoods of all earlier prefix vertices prevents repeated vertices and chords, while restoring the current endpoint permits its extension. Hamming distance and parity are necessary lower-bound conditions on the number of remaining edges. Reaching the target early is impossible for a simple path with fixed length; adjacency to the target while more than one edge remains would create a chord. Connectivity, component size and alternating colour capacities are necessary conditions for the remaining path. The colour formula counts the required vertices of the start colour correctly for both edge parities. None of these rejection rules was found to remove an actual completion.

During the second phase, the completed first path remains at the top of the first frontier. Each surviving representative receives its own second search after all contacts with the complete first path are removed. The first path is removed only after every pending representative is exhausted. This preserves enumeration coverage at ordinary loop boundaries.

## Checkpoint defect and permitted interpretation

The reviewed worker has non-atomic frontier transitions at lines 116–117 and 137. A `KeyboardInterrupt` after `pop()` but before completion of `extend()` removes a prefix without recording all its unexplored children; line 117 can also be interrupted during generator consumption. Lines 121–122 similarly remove the current representative before installing the next representative's initial second frontier. An interruption between those operations can cause the next representative to be treated as exhausted without search after resumption.

The handler at line 139 saves these states as `INTERRUPTED`, and the resume branch currently accepts that status. A later `EXHAUSTED` result from such a resume would lack coverage justification. The recommended correction is to construct each complete successor state before replacing the current state with one assignment, and to reject interrupted checkpoints produced by the reviewed version. Parent communication confirms that this correction will use a new worker version and that the live worker bytes were preserved until its ordinary timeout. No revised worker is covered by this initial review.

Ordinary time limits are checked at the top of the loop, outside these transitions. Periodic checkpoints also occur at this boundary. The observed terminal TIME_LIMIT checkpoint therefore retains the unvisited search work. A resource-driven process termination can leave a prior atomic checkpoint, which may repeat work when resumed; a terminal resource receipt alone does not establish exhaustion. The execution label `ACCEPTED_NATIVE_RESULT` must always be interpreted together with the worker result status.

## Witness audit and terminal limits

The reconstruction replaces both inclusive 44-edge source intervals by 45-vertex paths, retains the source vertices outside those intervals, and appends vertex 24. The final assertions independently require each replacement to be induced, the complete sequence to have 193 distinct vertices with exactly consecutive Hamming-distance-one pairs, endpoints 0 and 24, and exactly four coordinate-8 crossings. These assertions validate an actual 192-edge witness if reached. An assertion failure produces ERROR rather than an exclusion. The reviewed run reached no candidate requiring this audit.

The observed `shared120/result.json` has SHA256 `dd86a4573405ce26b92f81c8ca8e24a743705351dee3423ad55daca1e30976c4`. It reports TIME_LIMIT at 120 seconds, 5,157,314 first-prefix visits, maximum first length 38 edges, no completed first path, no second-prefix visits, 14 pending first prefixes, and `exclusion=false`. Its execution receipt has SHA256 `ea5f7dfb6e4d43e23bced09ef4c847a6ebd8664d6a855b3f8138db44b68e67d0`, terminal exit code 0 and no stop reason. These are saved native observations, not an independent rerun.

No seven-context exclusion, new witness, global snake bound, or Lean traversal certificate follows from this bounded run. Even an eventual sound native exhaustion would apply only to the five representative tasks and their stated seven-context reduction, conditional on the pinned input restrictions.

## Addendum: atomic successor and exact timeout transfer

Read all of `prepare_atomic_worker.py` (15 lines), `shared_paths_atomic.py` (142 lines), `transfer_checkpoint.py` (19 lines), and the transfer record and transferred checkpoint. Inspected the complete original-to-successor source diff and compared the complete parsed original and transferred checkpoint objects. This addendum is source and saved-data review only; neither worker nor the preparation/transfer scripts were executed by this reviewer.

| File | SHA256 |
|---|---|
| `scripts/prepare_atomic_worker.py` | `0934802d43393a229572ae58e795a9f82e5dea4aefd1af389045c4c85c9313db` |
| `scripts/shared_paths_atomic.py` | `ea5a24694aac0b18b8ceb10f6ff8d54c7fe0114c4c6cfdc9abd2ee08612e6a5b` |
| `scripts/transfer_checkpoint.py` | `554942d0ec83bb3959fb8208622909fa2b3a44b5ed798e7b7b2675d129385481` |
| `scripts/run_shared_atomic.py` | `98dfc99296510ec0faaeceddab5d51d3f35782116105df3561f8608d0c9c1830` |
| `data/checkpoint-transfer.json` | `40894d6ae59683639e6ed7c4a316287488f432514b7da12052246f39d98a1ca9` |
| `data/shared120/checkpoint.json` | `dafdd9f212d06f01ce1aac1ff5f49679de99cfed1c10a54d975bcd0b7303746b` |
| `data/shared120-atomic-checkpoint.json` | `22ca6401e59c5f7e4b512976939bbb00dbf7502ddf4b14ce18ad9ee8c0108a64` |

The original worker remains byte-identical to the hash in the initial review. The complete successor diff changes five state-update locations only. Each affected transition now constructs fresh lists and a complete successor dictionary before assigning it to `state`. No pending list or prefix is mutated during that construction. An interruption before the assignment leaves the preceding complete state available; an interruption after it leaves the complete successor. This repairs the identified loss of unexplored first children, second children, and pending representative searches. The first-to-second transition and final representative-to-first transition also replace their whole state together. The successor clears exhausted second-phase lists when returning to the first phase, which does not change the search.

All adjacency, representative reduction, domain, capacity, extension, branching-order, witness and stopping rules are unchanged. The generated atomic runner differs from the original runner only by substitution of the worker filename. The repair concerns enumeration state: counters can still be incremented before an interrupt and incremented again when that state is resumed. This can overcount visits without discarding any search branch. An interruption after removing the very last pending item but before assigning EXHAUSTED can leave an empty-frontier INTERRUPTED checkpoint that the existing resume assertion rejects; this is a resumption limitation and cannot create a false exclusion.

The transfer script accepts the particular original checkpoint only after confirming an accepted terminal execution receipt, exit code zero, no external stop, every execution pin, the result hash, the result-to-checkpoint hash link, TIME_LIMIT status, and the original worker hash. Direct comparison confirms that the actual destination differs from the original parsed checkpoint in exactly `pins.script_sha256`. All pending paths, option lists, counters, elapsed time, phase, status and remaining pins are identical. Both transfer-record file hashes match their actual files. The original execution receipt remains `ea5f7dfb6e4d43e23bced09ef4c847a6ebd8664d6a855b3f8138db44b68e67d0`; all its current input pins and both result/checkpoint links match.

The transferred state is therefore the same clean top-of-loop TIME_LIMIT frontier: phase `first`, 14 pending first prefixes, no second prefixes, no pending second options, and `exclusion=false`. The new worker pin matches the actual atomic successor. The script provides no route for transferring an original-version INTERRUPTED checkpoint; direct resumption of an unmodified old checkpoint by the successor also fails the differing worker pin. The original defect and its restriction remain applicable to the preserved original source.

The parent reports that separate CP exclusions now supersede these five DFS tasks. Those CP models and terminal results are outside this addendum. Preservation and transfer of this frontier establish continuity of pending work only; they do not turn the recorded DFS timeout into exhaustion. No blocker remains in the reviewed atomic repair or this exact timeout transfer.
