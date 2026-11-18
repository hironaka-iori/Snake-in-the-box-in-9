# Round 237 resumption review

Status: PASS for the inspected mathematics, source interpretation and read-only finite reconstructions below. Current proof compilation remains the parent's responsibility. No solver, compiler or software test was run by this reviewer. Original research sources were preserved; new split proof sources and this report are the reviewer's only changes.

## Cube inverse and two missing observations

Read the complete original `parity/CubeInverse.lean` and its saved compiler log. The source defines the actual nine-dimensional Boolean cube recursively. Its neighbour sum changes every coordinate once; its inner product enumerates every bit vector. It proves self-adjointness, translation compatibility, the complete coefficient identity and point-mass evaluation. Consequently the reconstruction theorem has no unproved geometric coefficient premise.

The two-erasure proof is also on this actual cube. At the two antipodes it obtains a two-by-two integer system with diagonal 128 and common off-diagonal coefficient in `{0,35,-10,8,-16}`. A difference of binary selections is bounded between -1 and 1, and its neighbour sums between -9 and 9. Finite coefficient and selection-value cases force the two missing observations to vanish. `determine_selection` explicitly supplies the difference of Boolean indicators. Thus the source states recovery from any 510 of the 512 neighbour counts, without requiring the two omitted vertices to have a particular parity or distance.

The four old log reports use only `propext`, `Quot.sound` and, for the recovery statements, `Classical.choice`. However the original source, log and object were loose files without a hash-bound command/exit receipt. The parent's fresh monolithic attempt stopped after about 6.2 seconds at the memory limit, before any axiom report; its compiler log is empty. That unsuccessful fresh replay must not be called an accepted check.

The reviewer prepared a memory-bounded decomposition at the parent's request. `logs/cube-inverse-split-plan.json` lists 20 modules and their hashes. The recursive algebra is shared. Sixteen independent modules each prove 32 cases with four leading bits fixed. A 16-way Boolean elimination reassembles the full 512-case coefficient theorem. Reconstruction and recovery are split at theorem boundaries. Original `parity/CubeInverse.lean` and the failed source snapshot remain unchanged. At this report's creation, these split modules were prepared but not compiled by the reviewer; use the parent's eventual receipts to determine their accepted status.

A subsequent source inspection found 18 punctuation characters in the newly generated reconstruction dispatcher had become literal question marks during the Windows text pipeline. These were replaced using explicit Unicode code points. All 20 generated modules were then scanned for question-mark and replacement-character corruption, and all plan hashes were refreshed. The repaired reconstruction source hash is `ba7f2c4ec6767a40c388996512ac31469ce751981b7c1cf33d9bd3cf020c7950`. No compiler was run during this repair.

## Archived majority degree models

Read `degree/majority_survey.py` and `degree/audit_majority.py` completely. The model fixes 97 selected majority vertices, 96 selected minority vertices, 95 retained vertices from the saved 96-set and exactly two selected majority endpoints. It enforces the appropriate degree only at selected vertices, leaving all opposite-class choices and endpoint locations free. Every target snake in this family satisfies the constraints. Disconnected cycles remain permitted until separately excluded.

The review applied the read-only inspection function to all archived models, without invoking its file-writing main routine or a solver. All 145 models matched the intended domains, exact linear rows and positive selection guards. Each has one initial iteration, recorded as `INFEASIBLE`, and no cycle cuts. Source, base, inherited base-input and model hashes match. These checks establish the model interpretation; infeasibility remains a native solver result without Lean contradiction replay.

## Enumeration and cut mapping

Read `degree/independent_screen.cpp`, `degree/independent_check.py`, `majority/cuts.py` and `majority/make_cut_proofs.py`. The second screening program rebuilds immutable neighbourhood masks and does not use the first program's deletion pruning. Both one-addition prefixes of a viable final set must satisfy the four-unit degree-deficit bound. Its duplicate-edge condition is sound: the alternative common neighbour already touches both selected endpoints, so a selected degree of two means that it labels the same pair.

The separate circuit model requires all 97 majority vertices and one dummy to participate, allows both directions of every simple contraction edge, and gives the dummy unrestricted neighbours. Removing the dummy from the single circuit yields a spanning path. The saved report records 623 native `INFEASIBLE` outcomes. Current source/checker/base/decision-archive hashes match that report. The review did not rerun the 177,062,400-description screening or the solver calls, and did not freshly locate the independent executable to verify its recorded binary hash.

The following read-only reconstruction was performed independently of either graph producer:

- Rebuilt every edited set from the base, deletion and two distinct outside additions. All 679 descriptions represent exactly 623 distinct 97-vertex same-parity sets; each description within a group gives the same set.
- Rebuilt each contraction from all 512 literal cube labels and their nine neighbours, deduplicating unordered partner pairs.
- Recomputed all 623 escaping-edge counts and positive cut excesses. Excesses 2, 4, 6 and 8 occur respectively 161, 291, 167 and 4 times.
- Parsed every certificate declaration. The indices are exactly 0 through 622, without repetition, and all selected masks and source/target lists agree with the reconstructed inputs. The dummy is absent from each source set and present in the original target set; deleting it accounts for the extra two in the path inequality.

This establishes that the saved 623 declarations refer to the intended numerical instances. Kernel acceptance, the literal-graph interpretation and the general path cut theorem remain distinct obligations. The old interrupted run had no final `kernel-cuts.json`; the parent's current execution determines the completed replay scope.

The read-only reconstruction is now preserved in `scripts/audit_finite_inputs.py` and was executed successfully to produce `data/finite-input-audit.json` with status `PASS_FINITE_INPUT_AUDIT`. It reconstructs all 145 archived degree models, 679 descriptions, 623 distinct sets and cut graphs, and all 623 declarations across 25 original certificate modules. The receipt pins its own source, the reviewed inspection function, inputs, inherited base pins and every declaration source. It does not rerun the full screening, a solver, or a compiler.

## Contributor upper bound 231

Inspected the exact Git objects at `478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088`: final source, both final audit logs, audit procedure and the ordinary `Snake9` definition. The final source states `forall {m}, Snake m -> m <= 231`, with no explicit remaining certificate or floor premise. The inspected snake definition is an injective ordering of `m+1` vertices in the 512-vertex cube, whose adjacency is exactly at consecutive indices; length therefore counts edges.

The saved final audit and its rerun report only `propext`, `Classical.choice` and `Quot.sound`. They report checking hashes of 24,797 certificate interfaces and 1,858 locally rebuilt specification modules, using a clean import-artifact directory, with `AUDIT PASSED`; the rerun records `EXIT 0`. The audit procedure checks published certificate interfaces against their worker manifests and rebuilds the specification/support layer. This supports reporting the contributor's completed, audited 231 theorem and a maintained interval of 191--231, attributed to that pinned record. A fresh independent rebuild of the complete certificate and dependency closure was not performed here and remains a limitation. The construction search should not claim this as its own new upper bound.

## Scope for manuscript integration

The present evidence excludes a candidate majority class retaining exactly 95 vertices from a saved 96-set. Together with the prior fixed-majority and three-replacement minority covers, majority overlap is at most 94 and minority overlap at most 92, giving at most 186 shared vertices. The seed has 192 vertices and a 192-edge candidate has 193, so at least six seed deletions and seven additions are required. Inverse cube isometries transport this restriction to copies of the saved seeds. It is relative to the bank and does not prove a global optimum.

The provisional manuscript anticipates complete kernel acceptance of all cut statements. Reconcile it with actual final receipts before integration. Acceptance of numerical statements alone does not silently establish enumeration coverage or their graph-to-path interpretation.

## Current local SHA-256 values

| File under this milestone | SHA-256 |
|---|---|
| `parity/CubeInverse.lean` | `be734f4df85bbfebc7febedd9e48913556f78c46a8b0b9245c64351309e0a690` |
| `parity/compiler.log` | `95b557278bf500cd87fab4c98904fb554e541123b0d961aed9c6fe0ab2e1209f` |
| `parity/CubeInverse237.olean` | `2b22c6a48f92182f192813b28d615815e6ed43242a2be0d1c590243ccf61d6e0` |
| `degree/audit_majority.py` | `a21e0fc9f339f36659ad7001039e8ec59708530715cfde4d67526bec695d68aa` |
| `degree/audit.json` | `2f7b3cd6d17abd66aa1e481360194187e02fe1118a5763cccf79281cea2309b6` |
| `degree/majority_survey.py` | `121ed018e2a38e38d1ca1938b352e8c561384404b01f1650bb4ee264e5d84a34` |
| `degree/majority-one.json` | `64075fee8123aff8f80ae0576c93a41708b70572c7a81097fd209bb65c1b595c` |
| `degree/majority-one-models.zip` | `24a34d4984d7276623f6e0aa0f5c521da829c97de9f22121b003b111e74ab735` |
| `degree/independent_check.py` | `120bb67b88a4c6cc1d66e542712f23a9d598992dfbf948b06056750c1542293d` |
| `degree/independent-results.json` | `0a5958ac69e0421243d3a9318bf7c31395f4a80e6d4ccb016f8eb6d624e0b939` |
| `degree/independent_screen.cpp` | `e3c27a4b2ec456e30035ea1187b533f45bd23849fde1e3e3aa6693bed976bf1d` |
| `majority/decisions.json` | `0325ef1c4b6c9ad4f54bc957a5c6ad0e48449e6b657312aa77191a1001cfc5a5` |
| `majority/cuts.json` | `f61ab53d4584a26da10f27579460839bb98eb10957cdc0d5c4f9182fe85d5e3f` |
| `majority/CubeCut.lean` | `1c4b7f92de0f5528fc7c3b6ef9a7750d659be6a6778cabf181e3294619cb5e8f` |
| `majority/make_cut_proofs.py` | `d5d731f6ad3a99ce71b3d56b427fdc3b7cfe5502833691c650eb225bb75ee8df` |

## Pinned contributor Git-object SHA-256 values

| File at commit `478869ee` | SHA-256 |
|---|---|
| `milestones/36-lean435-port/audit231/UpperBound231_435.lean` | `69ab256391f0b00a5c3e1000a4ed7e21e19394cecf8435ea327fdf44a2f23c05` |
| `milestones/36-lean435-port/audit231/final-audit.txt` | `aeae11af6a8873cd93a4f5e824f63f31f90f0824531ca6448ee7fee1f874b14a` |
| `milestones/36-lean435-port/audit231/final-audit-rerun-out-olean.txt` | `37a4f1b61486ef90772170c71522d1b72b4188aa445df8c0c28ed0d5a4f02384` |
| `lean435/tools/audit.py` | `e27f41349bce09c02a2032c92705cfdffdf0ca844143c075d6f6a9889737053f` |
| `work/final_lean/Snake9.lean` | `025260b9c1533d606a6cfd058aa025d9544d5cd6ccb1f8f5f2143e5657df4740` |
