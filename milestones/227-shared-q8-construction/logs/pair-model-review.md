# Reduced path-pair model review

Read the complete `scripts/pair_cp.py` source and used the already reviewed, pinned companion data. No blocking mathematical defect was found. This is a source and small finite-data review; no solver, compiler or software test was run, and no solver outcome was assessed.

## Mandatory domain reduction and exact counts

Each path must avoid the other path's mandatory anchors and all their neighbors. Removing those closed neighborhoods before variable creation is necessary because the two lower paths occupy separated portions of the full Q9 path. All mandatory own anchors survive this reduction in the five default tasks, as independently checked from the saved lists.

| Configuration | First reduced domain | Second reduced domain | Second edges | First even vertices | Second even vertices |
|---|---:|---:|---:|---:|---:|
| 0 | 99 | 99 | 33 | 22 | 17 |
| 1 | 98 | 99 | 32 | 22 | 16 |
| 14 | 98 | 99 | 39 | 22 | 20 |
| 15 | 98 | 98 | 38 | 22 | 19 |
| 16 | 97 | 97 | 35 | 22 | 18 |

The first path has 43 edges from 18 to 224 and therefore 44 vertices. The second target and endpoints come from its configuration. The source fixes both anchors, the exact selected-vertex count and the even-colour count derived from alternating parity. Each default endpoint pair has the required edge-length parity. These equations hold for every intended path.

## Degree model and cycle cuts

For each selected vertex, the model counts all selected cube neighbors. Its required degree is one at each anchor and two elsewhere. Unselected vertices need no degree constraint. Consequently any connected feasible selected component containing an anchor is a simple path ending at the other anchor: a finite component cannot have exactly one odd-degree vertex, and a maximum-degree-two component with a degree-one vertex is a path. The remaining components have degree two everywhere and are cycles.

The extraction follows the unique next neighbor from the first anchor while excluding the previous vertex. Its assertions detect a repeated vertex or a violation of the expected degree structure. Each remaining connected selected component is separately collected and checked for degree two. A valid induced path cannot select every vertex of such a cycle, because the cycle's closing edge and all its other edges remain present in the selected induced graph. Thus the added inequality requiring at least one cycle vertex to be omitted is necessary for every valid connected path, independent of the previous model's selection. Applying these cuts cannot remove an intended path.

Cross-part rows prohibit equality and every cube adjacency between selected lower vertices from the two paths. Together with the companion-domain projection restrictions, these enforce the required separation from the upper pieces as well. The first model permits disconnected cycles, so a feasible relaxation alone is never accepted as a path witness. Extraction and added cuts continue until both selected components are actual paths or the native query terminates.

## Reconstruction and output interpretation

The source appends 480 to the first lower path and surrounds the second lower path with its saved upper prefix and suffix. It places both replacements at their recorded seed intervals, retains every other seed position, and appends 24. Before accepting a witness it checks the two lower lengths, all 193 full vertices, distinctness and the adjacency relation for every vertex pair, and exactly four coordinate-8 crossings. The endpoints are 0 and 24 by the fixed seed prefix and final append. The validation uses Python assertions, so the invocation must retain enabled assertions.

The prior enumeration review proves literal full-sequence identity across all seven configurations represented by task 0, and separately across those represented by task 1. A found compatible pair in either task therefore reconstructs that same sequence in all seven contexts. This observation uses exact saved sequences and domain equality; it introduces no symmetry assumption. Configuration 17 is omitted only under its already checked existential containment in task 0.

`COMPLETE_QUERY_BATCH` means that all requested tasks received a query record. It can include `UNKNOWN`, `TIME_LIMIT` or another nonconclusive native status, and must not be reported as an exclusion. Only a particular terminal `INFEASIBLE` supports that task's native exclusion. The exported model and its hash describe the initial relaxation; reproducing a later solve also requires adding the recorded cycle cuts in order. No independent native contradiction certificate or Lean traversal transfer is supplied by this script.

Custom task IDs and tags remain caller-selected input. The audited default list is exactly `0,1,14,15,16`. This review does not establish a compatible pair or resolve any native query.

## Frozen pins

- `scripts\pair_cp.py`: `ec05c49bb0ea401d65457155f5b5420aa7c6132b62aabd76da44546c18703412`
- `data\companions.json`: `301a7bc1fd4aac979d86729d9ecde695be39a808b9dbb6617a3e33390eade8dd`
- `data\regions44.json`: `c2c5b1465726c4e8c2ab142a1524e171cfeb992cb66d906475e9d1e2e766ec0b`
- `logs\upper-enumeration-review.md`: `01d2fbb7fa616c70aa7eb4251e1dd0d2a2f169258e34c60fa895da5ac95edf0d`
