# Remaining width-44 reduction review

Read the complete `prepare_remaining.py` and `remaining_cp.py` sources, all 35 context records and all 230 configurations. Independently reconstructed the finite upper enumeration, exact groups, strict domain-containment chains and default model task list. No blocking defect was found in the inspected sources and saved reduction. No solver, compiler or software test was run, and the live batch was not inspected.

## Coverage and forced allocations

The context IDs equal the saved round-226 width-44 unresolved set minus its seven shared-Q8 contexts: exactly 35. The two original anchor pairs, index intervals, all domain lists and global crossing budgets match the literal `regions44.json` rows.

Both first anchors lie in the lower face, so the first replacement has an even number of coordinate-8 crossings. In the six contexts with total replacement budget one, the second endpoints lie in opposite faces; hence the allocation is necessarily first zero, second one. These include four upper-to-lower orientations and two lower-to-upper orientations. In the other 29 contexts, the total budget is two and both second endpoints are upper. A zero-crossing second path would require 45 upper vertices, while each such prepared upper domain has fewer than 45. Therefore the allocation is first zero, second two. The first replacement is consequently entirely in Q8 and has 44 edges. Its anchors vary by context and are retained in each task key.

The upper-domain sizes across this family are 13, 14, 15 and 22. In particular none can accommodate an omitted 44-vertex upper piece; the enumeration's positive lower-length condition loses no zero-length lower-segment possibility in these concrete domains.

## Independent finite enumeration

A separate breadth-by-length construction generated every simple induced upper path, using a full pairwise check for each extension. Both one-crossing orientations were handled explicitly: an already-lower starting endpoint has an empty upper prefix, while an already-lower ending endpoint has an empty upper suffix. Two upper endpoints produce both pieces. Every pair was checked for mutual equality or adjacency, then its ports, projections, two lower domains and prescribed lengths were reconstructed. All 230 records match, including prefix/suffix node counts and context-to-configuration associations.

For upper pieces with $l$ and $r$ vertices, the lower segment has $44-l-r$ edges. Including the appropriate one or two vertical crossings gives a 44-edge second replacement. Upper projections are removed from the first lower domain and, except for the two lower endpoints, from the second lower domain. Independently checked all 230 records for unintended vertical adjacency between a lower endpoint and any nonattachment upper vertex; there are none. This matters particularly in the one-crossing cases, where only one lower endpoint is a vertical port.

## Exact groups and strict domination

The exact grouping key includes both first anchors, first edge length, first domain, both second lower anchors, second edge length and second domain. It reproduces all 79 saved groups. Thus changing first endpoints or lengths cannot silently identify different tasks.

For every containment step, both endpoint pairs and both prescribed lengths agree, both domains are subsets of the target task's domains, and at least one inclusion is strict. Increasing finite domain size prevents a cycle. Reconstructing the producer's immediate selections and following every chain gives exactly the saved flattened map: 27 dominated groups and 52 undominated representatives. Every final domination target belongs to those 52 representatives. The worker's default ID list matches their saved order exactly.

A compatible lower-path pair for a smaller-domain task is also a pair for its containing task because the inducedness and mutual nonadjacency requirements are unchanged. Dropping dominated tasks therefore preserves existence possibilities in the combined search. Their upper arrangements and complete Q9 witnesses need not be identical, so this reduction does not preserve individual configuration solution counts or establish a general symmetry.

## Model specialization and reconstruction

Compared with the previously reviewed `pair_cp.py`, the remaining worker reads the new configuration file, takes both first anchors and first length from each record, removes closed neighborhoods of those actual mandatory anchors, and uses the first lower path itself as the first replacement. It does not append 480. The saved default list contains all 52 representatives.

If mandatory anchors are removed by mutual separation, the worker records a necessary static infeasibility result before model construction. Otherwise the selected-vertex count, alternating parity count, anchor degrees one and internal degrees two are necessary for each intended path. Cross-part inequalities forbid every shared or adjacent lower vertex. The unchanged extraction and lazy cycle cuts retain the prior argument: anchor components are paths, remaining degree-two components are cycles, and an induced path cannot select an entire such cycle. These constraints introduce no extra fixed endpoints or lengths from the earlier shared problem.

For every configuration, symbolic assembly has 193 entries, begins at 0 and ends at 24. The first replacement has 45 vertices. The second concatenates its possibly empty upper prefix, the lower path including endpoints, and its possibly empty upper suffix, also totaling 45 vertices. The outside seed is unchanged. Its fixed crossings plus the forced second crossing count total four, while the first contributes zero. Acceptance still requires the full concrete distinctness/inducedness and crossing audit, with Python assertions enabled.

`COMPLETE_QUERY_BATCH` can include unknown or timed-out individual tasks. It is not a family exclusion. Exported model hashes describe the initial selected-degree relaxation; replaying a later solve also needs its saved cycle cuts. The input domains and the earlier restriction to unresolved contexts retain their native-evidence qualifications. This source review establishes no new witness, solver contradiction, global bound or Lean traversal result.

## Audit particulars and pins

- Exact configuration count: 230; exact groups: 79; strict dominated groups: 27; representatives: 52.
- Maximum reconstructed domination-chain length: 1.
- Default representatives rejected by the mandatory-anchor check: [].
- First anchor pairs and context counts: {(0, 96): 10, (1, 104): 14, (17, 232): 11}.
- `E:\Snake-in-a-box\milestones\227-shared-q8-construction\scripts\prepare_remaining.py`: `989c72b3a519a6f72aee73ee7f5fa3111d55164799e7c867961ba4b1bffd4577`
- `E:\Snake-in-a-box\milestones\227-shared-q8-construction\scripts\remaining_cp.py`: `31aa6313c3c786a1ca9f73ea102ceace9a3514d5252434655b17a486b18e5c4d`
- `E:\Snake-in-a-box\milestones\227-shared-q8-construction\data\remaining-companions.json`: `5116f98679a453bf59283246c3499712ad01b5638ad60d0983ff916be251603a`
- `E:\Snake-in-a-box\milestones\227-shared-q8-construction\data\regions44.json`: `c2c5b1465726c4e8c2ab142a1524e171cfeb992cb66d906475e9d1e2e766ec0b`
- `E:\Snake-in-a-box\milestones\226-connected-replacement-search\data\search-summary.json`: `7846398a8dcf8dfafca5c78229c30ed152760dafec6e11ac2a5afb8f7ea13e40`

## Terminal coverage addendum

The two terminal batches now supply 57 actual native infeasibility records: five shared-family representatives and 52 remaining-family representatives. Each has exactly one solver iteration, that iteration reports `INFEASIBLE`, and no cycle cuts were added. Thus the saved initial model is the model used for the contradiction in every one of these 57 cases. All 57 model hashes were checked.

Both execution records report `ACCEPTED_NATIVE_RESULT`, exit code zero and no resource stop. Their pinned sources, input data, result files and stdout/stderr hashes were checked against the saved bytes. The exact requested representative sets and order agree with the prior source review. No solver proof was replayed.

| Batch | Infeasible queries | Recorded batch seconds | Wrapper seconds |
|---|---:|---:|---:|
| reduced-pairs | 5 | 5.359000 | 11.250000 |
| remaining-pairs | 52 | 42.171000 | 43.468000 |

Read all of `close44.py` and independently reconstructed its configuration maps, every new cover entry and every updated context row. The prior 259 exclusions are carried forward unchanged: 107 static exclusions, 148 native infeasibility records and four prior two-port covers. Their recorded statuses were matched to the pinned underlying batches; each of the four port covers has both port branches recorded infeasible. The 42 new cover entries are distinct and equal exactly the prior unknown-context set. Every configuration maps to an actually infeasible representative through the previously checked equality or same-endpoint/length domain-containment relation. There is no uncovered or duplicated context in the 301-row final table.

For each of the seven initial shared contexts, the total replacement budget is three, the first endpoints are on opposite faces, and the second endpoints are both upper with fewer than 45 available upper vertices. Hence the first and second crossing counts are one and two. The first target's upper component is exactly `{480,488}`, giving the two possible suffixes `[480]` and `[488,480]`. The former is covered by the new reduced-pair contradictions. Each latter branch has an explicit earlier `ports44-232` infeasibility record, not merely an absent or filtered row. Its accepted execution receipt, source/result/output pins and the seven referenced model hashes were checked. These old contradictions retain their native qualification.

The final tally is 107 `STATIC_EXCLUDED`, 148 `INFEASIBLE`, four `PORT_COVER_EXCLUDED` and 42 `REDUCED_PAIR_EXCLUDED`, totaling 301. The summary's empty width-44 unresolved list, 57 reduced contradictions and coverage-file hash match this reconstruction. The earlier `shared120` DFS remains `TIME_LIMIT` with its accepted execution and checkpoint pins intact; it supplies no exclusion and is not used by the cover mapping.

No logical coverage gap was found in this bounded audit. The supported conclusion is complete **native exclusion of the specified fixed-seed, endpoint-24, two width-44 length-preserving replacements with exactly four coordinate-8 crossings**, incorporating the inherited exclusions and both first-port branches. It is not a global snake upper bound and is not a Lean contradiction or complete traversal certificate. No solver, compiler or software test was run during this audit. The mathematical validity of the earlier prepared domains and historical pruning retains its previously recorded scope; this addendum verifies the terminal assembly rather than rebuilding every historical proof.

Terminal evidence pins:

- `milestones\224-cross-block-reconnections\data\pair44-execution.json`: `477d3aee31ea8c0c537c2d3cef5f746533465a9dc940014b62b4102946eae9b4`
- `milestones\224-cross-block-reconnections\data\pair44.json`: `f1385f1f86fd4ad2d6e4c2ca16160a14d5ff77cba6c9baefac4cbc18d5f10417`
- `milestones\226-connected-replacement-search\data\boundary44-execution.json`: `630f6d0447d8c7394ebac664252e8b2a95de6c41501b46b8e476f83339e74985`
- `milestones\226-connected-replacement-search\data\boundary44.json`: `d4698f8d4ea7f652ee6759e76e3b469af0e463d5a38dc8bccc9029afd8e74ac4`
- `milestones\226-connected-replacement-search\data\combined44.json`: `568a562743752b9857b377035ff7d59551b41ee49b4b671bce408bb3c8983fb1`
- `milestones\226-connected-replacement-search\data\port202-224-execution.json`: `bb907e38523f952adbce650a1ec2e4e730ce6eb9ef000da063320ebf4d1374a7`
- `milestones\226-connected-replacement-search\data\port202-224.json`: `bdf43e268af5746c4554f9a34b686e599cb3dcc6a0da69465880379a5404d5f7`
- `milestones\226-connected-replacement-search\data\port202-232-execution.json`: `3799bb914ff4aa7b94e59828115c0dc58021867542723335eb30af9f0df9079d`
- `milestones\226-connected-replacement-search\data\port202-232.json`: `cf37228a217d1bc0d6310011c1d5e8f7df01dbe8d93df1e959057fd0826726a4`
- `milestones\226-connected-replacement-search\data\ports44-224-execution.json`: `db28d53d48463f2f68b7e3026faa193a840ffe92117b0151ffb1170c6ec18bc2`
- `milestones\226-connected-replacement-search\data\ports44-224.json`: `8819777da6d712772aa20ee99953a6f774bb582c1aeabfb68ccbc45d4c7df058`
- `milestones\226-connected-replacement-search\data\ports44-232-execution.json`: `2030f147216be2593b319d6740391a343e54b9626858e64c4e78a6369d3f311b`
- `milestones\226-connected-replacement-search\data\ports44-232.json`: `4e854615c0e14dd818be81e97fbef8b2c733a443c32b343e0baba08481600073`
- `milestones\227-shared-q8-construction\data\companions.json`: `301a7bc1fd4aac979d86729d9ecde695be39a808b9dbb6617a3e33390eade8dd`
- `milestones\227-shared-q8-construction\data\coverage44.json`: `f02bfee405ddc56db3923d246ea245c035f9fa19bb6132923524d46ff64e01a5`
- `milestones\227-shared-q8-construction\data\reduced-pairs-execution.json`: `010078be4112f3883d5fd1da0b3836e0d553fc59dfeaf0e4ea8ecccf231f7827`
- `milestones\227-shared-q8-construction\data\reduced-pairs\result.json`: `80f4de68a0a1efb16da310edae8fbabf10195195fe80b721844cfe384926fcc8`
- `milestones\227-shared-q8-construction\data\remaining-companions.json`: `5116f98679a453bf59283246c3499712ad01b5638ad60d0983ff916be251603a`
- `milestones\227-shared-q8-construction\data\remaining-pairs-execution.json`: `5caf8e6d09ff4e8b97ab0bb4b64f63b909ce300602ba510b6dadea1b5c7fc9e6`
- `milestones\227-shared-q8-construction\data\remaining-pairs\result.json`: `0aabfce7de02ef08ec79a3d3ab9a8d3b6c5fac712a947150694158dfb19827af`
- `milestones\227-shared-q8-construction\data\search-summary.json`: `7ba92ae16c661c862fb8552617db14ff075b02c8988410a650a6b8b987af0e6a`
- `milestones\227-shared-q8-construction\data\shared120-execution.json`: `ea5f7dfb6e4d43e23bced09ef4c847a6ebd8664d6a855b3f8138db44b68e67d0`
- `milestones\227-shared-q8-construction\data\shared120\result.json`: `dd86a4573405ce26b92f81c8ca8e24a743705351dee3423ad55daca1e30976c4`
- `milestones\227-shared-q8-construction\scripts\close44.py`: `02b1f5567af5d21d5d5acfcc51dba5444da4a6ee8958b64600ee6c90fc01acbe`

The preceding review bytes were preserved verbatim; their pre-addendum SHA-256 was `5745f208206c0dbc3e89170dce239e83f2ca49a3b8d06547250bd53ae2357226`.
