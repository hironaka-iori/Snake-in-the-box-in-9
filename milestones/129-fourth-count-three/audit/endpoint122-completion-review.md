# Completion audit of the milestone 122 endpoint theorem

**Result: PASS_448_ENDPOINT_MODULE_RECEIPTS_AND_ACTUAL_ASSEMBLY.** The saved endpoint batch completed on 3 November 2026 at 07:02:15 UTC. This independent audit completed at 07:29:16 UTC and took 100.735 seconds. No solver, Lean compiler or native proof replay was launched. No file in milestone 122 was modified.

The endpoint result is now proved for actual snakes under the stated window and count hypotheses. The three local certificate premises that were explicit in the earlier assembly theorem are discharged in `ActualEndpoint122`. This completion does not by itself improve the global upper bound.

## Exact mathematical result

Let \(p_0,\ldots,p_m\) be an induced path in \(Q_9\), with length measured in edges. Suppose \(r+6\le m\), the six directions starting at \(r\) have canonical word \(012032\), and the actual counts satisfy

\[
\alpha_{r+2}+\alpha_{r+4}=8.
\]

Then both specified centres are at Hamming distance two from both endpoints:

\[
d_H(p_{r+2},p_0)=d_H(p_{r+2},p_m)
=d_H(p_{r+4},p_0)=d_H(p_{r+4},p_m)=2.
\]

For every finite set \(I\) of starts satisfying these fitting, canonical-word and actual-count-equality hypotheses,

\[
|I|\le13.
\]

These are the statements `Snake9.ActualEndpoint122.actual_equality_endpoints` and `Snake9.ActualEndpoint122.equality_count_le_thirteen`. The final statements contain no unproved local-refutation parameter. They do not assert that thirteen occurrences can be attained or that thirteen is optimal.

The local certificates cover count caps \((2,6)\), \((3,5)\) and \((4,4)\); reversal covers \((5,3)\) and \((6,2)\). The previously checked pair minima and equality of the sum to eight reduce all cases to this list. The three local certificates force every endpoint into the fourteen-vertex common distance-two sphere in canonical coordinates. The geometry module transfers that location back to the actual snake.

The count of thirteen uses both centres. The common distance-two spheres of two distinct endpoints contain at most fourteen vertices. The positions \(r+2\), for \(r\in I\), are distinct, and the additional position \(\max(I)+4\) lies beyond all of them. When \(I\) is nonempty, these give \(|I|+1\) distinct vertices in the intersection, hence \(|I|\le13\). The empty-set case is immediate.

## Checked coverage

The completed pending run contains 381 modules. Combined with the 67 earlier modules, the audit covers all 448 Lean sources currently in milestone 122: 436 certificate modules and twelve supporting or assembly modules. No source module is missing a matching successful receipt.

| Certificate | Modules | Selected inputs | Deductions | Hints | Receipt coverage |
|---|---:|---:|---:|---:|---|
| Count caps \((2,6)\) | 58 | 3,886 | 2,925 | 1,045,855 | Complete |
| Count caps \((3,5)\) | 164 | 3,788 | 10,275 | 3,072,560 | Complete |
| Count caps \((4,4)\) | 214 | 3,909 | 19,349 | 3,997,908 | Complete |

The last pending run also checked `LocalEndpoint35122`, `LocalEndpoint44122` and `ActualEndpoint122`. The final actual-snake module completed successfully in 21.047 seconds. Its two printed axiom reports contain exactly `propext`, `Classical.choice` and `Quot.sound`.

Across all 448 modules, the audit matched all thirty printed axiom reports to their saved logs and receipts. Six reports belong to the newly completed 381-module batch. Every reported axiom belongs to the same permitted three-element set; no `sorryAx` appears. The source scan found no `sorry`, `admit` or `native_decide` token in the checked module set.

For every module, the audit verified the current source, preserved source snapshot, compiled object, compiler log, checker snapshot, dependency pins and directly resolved import objects. It checked the actual import search order and the receipt links between local modules. Every receipt also has a matching successful record in a saved run. Older runs marked `STOPPED` remain preserved; only their individually completed module records were counted.

Two checker-script versions occur in the historical receipts. The three modules `EndpointAssembly122`, `EndpointFrequency122` and `EndpointGeometry122` use snapshot hash `1be4a07d463808b6067e100c2368a66874580750861d73f8381bce9c2f241b51`. The other 445 modules use `fa12c17b80dca5e01115678cd0bccdac493a95e7290afe702729a82f79d88823`. Each was verified against its own saved snapshot; the audit did not assume a single script version for all historical runs.

The certificate plans, original and ported source hashes, CNF and LRAT hashes, native solver records and recorded source dependencies also match. Original-to-ported text comparisons permit only the recorded local import prefix. The endpoint checker’s isolated namespace and increase of literal-parser fuel from 255 to 1023 were checked against its source-port record and successful receipt.

In total, the completion review records 2,880 verified file hashes. It verifies dependency receipts and directly resolved objects without rerunning every historical transitive proof job. Native proof counts in the table come from the pinned export records; this completion audit does not repeat native LRAT replay.

## Terminal state and preserved history

`pending-progress.json` has status `PASS_ALL_ENDPOINT_CERTIFICATES_AND_ACTUAL_ASSEMBLY` and no active child. Its bytes match the archived driver record. The underlying 381-module run has status `PASS_REQUESTED_MODULES`, with all 381 expected successful receipt entries. Both milestone 122 lock files are absent. A read-only process query found no process with the former driver PID 55040.

The pending plan and earlier 67-module review retain their original historical statuses. Their references to pending certificates have been superseded by the present completion evidence, and their bytes have not been rewritten.

## Pins and limits of the conclusion

The complete verification record is `milestones/129-fourth-count-three/data/endpoint122-completion-review.json`, SHA256 `936d8277d0421ca548e6db1240d85b295e4a5af950067aa9e73cf8a858ff9dcd`. It includes exact theorem assumptions, source statements, module coverage, import resolution, all thirty axiom reports through their module records, and the file-hash inventory.

The final `ActualEndpoint122` evidence has these SHA256 values:

| Evidence | SHA256 |
|---|---|
| Source and preserved source snapshot | `9175c0701730bd321070b7d0398fbb1f16e633ef05ccc6a6296ca4bb3af1d497` |
| Compiled object | `f831e1d68acf388a3fcb6eb7048bce6e18eee147405e202b8f2d0263a84329a2` |
| Compiler log | `78b99a8aa89952395da982de567b98ef4b40a5dd935fa4a1ad3e0ab805c67e4c` |
| Successful module receipt | `995c50cac30be96682e4b794f577ebaf19ce4d02b74c47004f2b88b1f9e6b7d1` |

The theorem supplies a proved occurrence limit for the specified actual equality windows. Applying it to a finite graph still requires a checked correspondence between graph credits and those actual windows, followed by the required charge and potential assembly. No new numerical upper bound for the longest snake is asserted by this audit.
