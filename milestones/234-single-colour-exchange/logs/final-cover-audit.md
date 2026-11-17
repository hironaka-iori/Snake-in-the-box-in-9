# Final candidate coverage audit

## Source review and execution scope

The independent final auditor is prepared in `scripts/audit_final_cover.py`. It has not been executed by this reviewer. The parent will execute it after the separate full static audit. The saved static audit now reports all 2,227,200 decisions checked successfully; the final auditor requires that successful receipt and its accepted execution record before proceeding.

The auditor reconstructs the equality grouping of the 1,381 surviving descriptions into 1,325 selected 96-vertex sets. It then rebuilds every candidate graph directly from Hamming distances. Each opposite-colour vertex with one selected neighbour supports an endpoint; each with exactly two selected neighbours labels the corresponding edge. Parallel labels are retained as metadata, while the circuit graph uses one edge per endpoint pair. All other labels are unavailable.

All 793 exported circuit models are checked, including the 712 models whose classes also have elementary certificates. Their Boolean variables and sole circuit constraint must match the reconstructed directed graph exactly, including both orientations of every internal edge and both dummy arcs at every endpoint-supported vertex. Every one of the 96 selected vertices and the dummy must occur, and no self-loop is permitted. Removing the dummy from a selected circuit gives a Hamiltonian path with supported endpoints. Internal labels for distinct edges are distinct, and singleton endpoint labels cannot coincide with internal labels. Thus this model preserves every induced 193-vertex path with the prescribed minority class; it imposes no fixed ordering, crossing count, or extra symmetry restriction.

The initial native batch remains `TIME_LIMIT`, with 771 completed `INFEASIBLE` rows. The second batch contains 22 completed `INFEASIBLE` rows. The auditor checks both execution receipts, source and input pins, model hashes, result and log hashes, and recorded resource samples. It does not promote the initial batch to a complete batch.

The previously completed elementary replay excludes 1,244 classes. Its source was inspected: forcing at available degree two, deleting unused incident edges at forced degree two, degree contradictions, and a proper forced cycle are necessary Hamiltonian-cycle rules. The final auditor checks the replay's complete status, source/input pins, every initial graph, individual trace hashes, operation counts and terminal records. It does not repeat the elementary step replay. Exactly 81 classes remain dependent on native infeasibility, comprising 59 initial-batch classes and the 22 completion classes. The union must equal all 1,325 candidate IDs with no unresolved class.

The script uses only Python's standard library and checks that assertions are enabled. It prints a machine-readable receipt for the parent to preserve, and appends the executed outcome below only after every audit assertion succeeds. No optimizer, compiler, software test, or repeated full static scan is invoked.

## Limits

Native infeasibility is accepted as recorded solver evidence; no native contradiction proof is replayed here. The exact finite reconstruction and previously completed elementary replay are separate from an end-to-end Lean connection to these concrete graphs. Any resulting exclusion concerns one-vertex replacements of the saved 96-vertex minority classes. It does not exclude arbitrary 192-edge snakes or establish a new global bound.

## Executed final coverage audit

Status: `PASS_COMPLETE_CANDIDATE_UNION_COVER`. The full independent static audit passed before this audit began. Exact grouping gives 1,325 classes from 1,381 candidate descriptions. All 1,325 graphs and all 793 exported native models match direct reconstruction.

The pinned complete elementary replay excludes 1,244 classes. Exactly 81 remaining classes have verified native infeasibility models/results: 59 from the initial batch and 22 from the completion batch. Their union covers all 1,325 classes. The initial native batch remains correctly labelled TIME_LIMIT despite its 771 completed infeasibility results.

The existing elementary step replay was not rerun; its source, input, individual trace, and reconstructed initial-graph pins were checked. The 81 essential native contradictions remain solver evidence. No optimizer, compiler, or software test was invoked.

Graph roster SHA-256: `316e5c0fc364855c8b5028219f6f238ab48a1bb1d733ce25aad1c3a00cd6c764`. Model roster SHA-256: `cf3a67c1a1a4b49dc28d3256f393cac6cd41bc70dd1865aac907f9cba2e53c61`. Auditor SHA-256: `41a08d6d3dfbe223f71f453d1fd9cae2833613fb84a527ca5a6337db9a7269e5`.

Compact evidence pins (individual model hashes remain in the pinned native-result files):

- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\scripts\audit_final_cover.py`: `41a08d6d3dfbe223f71f453d1fd9cae2833613fb84a527ca5a6337db9a7269e5`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\exchange-audit.json`: `0eef4aaf9ec6441a32904eb21270ffa3a906eee97b7cad092a0c7eb526d24be4`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\bases.json`: `ff2356155763cb4bf8f2d1eff80f893021793deca4c76e9183f990ecb6b3297b`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\exchange.json`: `bf75550ff4760a88713b1c469c7971e2bea75cdac3e77398d92590a7acfb60ca`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\exchange-decisions.bin`: `b538167ca664ab2e57f66e45480074717cb716831e65182a2045d3564cc5dd4f`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\exchange-execution.json`: `52bb3e98199e85d06fa8c191b226f2459f666b8e380664ebaeaa71c015c1330a`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\scripts\exchange.py`: `8b478ce38211257008ad588757137bfb68a44c65afe6bfb7430b73d4be7bc913`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\scripts\run_exchange.py`: `f7e872966f5512129ba2876602c3718e72eb6ab7e086d4032ae71c9d0f14f50b`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\scripts\native_resources.py`: `2e9e7d499ef7068d10d7ca7e31c9a9dc7ef19abb72b0396d3eab9824376b4413`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\scripts\audit_exchange.py`: `0f382159c8a09236e37d1fde2ed21aa86122d44b2cca3ccb21f75e1790b918a0`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\exchange-audit-verified-execution.json`: `416c0fe2f3bac0858af5b0564e76e3c96f71e3749a8f3007bc2d874734fc9db0`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\scripts\run_audit_verified.py`: `386c61a156268ef4bca0d577b29a594f852c6541242f60125f0b1a7d5678c3a7`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\logs\exchange-audit-verified-stdout.log`: `6d055c81c985daa9c3e290f3082259538f37d6027c624b9975dc45d5032a822c`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\logs\exchange-audit-verified-stderr.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\candidates.json`: `e3575cbb703e242fc9251509cf25637a7a94223b2371973fe243a00474e3e0b4`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\forced-cycles.json`: `6d2cb01fe6539224b884d5a7c2305c89371589e9dd3e2a781857b9034e3ad01b`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\forced-replay.json`: `1c271e2d4e082667542b8666a9c164c11e718412c71161dbd0424f2bf434dd91`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\scripts\replay_forced_cycles.py`: `fb823a5314995f95d625b274989861bfc8ee5712dc8eb678bc0de69aefdab016`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\scripts\forced_cycles.py`: `dfc03e1bd81ba2fbb5995cb523b29941f602bf8af9e687fcc3a24d84ccf18c30`
- `E:\Snake-in-a-box\milestones\231-endpoint-exchanges\data\colour-survey.json`: `5e7ee3e1e685f4715538d155f9d095e303c75f5de48270faead094bd2f569d9d`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\forced-cycles-execution.json`: `197e0bf16d428e4d19b8425ffd18da9cbafbf17fb36b67c14729e0da14ed6f2f`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\scripts\run_forced.py`: `7408805ea25a95e520cca0f6fb8fc8e6a22be478ae61c5afe842eee3518c7594`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\logs\forced-cycles-stdout.log`: `a69fa9025c868b1646599b018c04b003ba634276f8ed6934b1c205e26c830875`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\logs\forced-cycles-stderr.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\hamilton.json`: `1bf077a1e893b5dcd09b2a29e2f14da840ffbec8eeed7d9832321eb0f00c659e`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\hamilton-resume.json`: `8e7fca32a0baee2416d29e49320155980d9d7885b040d5de23bdbc81bcccfa01`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\remaining.json`: `14bcc9823c1e94ad8e02513b338bddee481523f8e86b146f83bf930c0d46af20`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\hamilton-execution.json`: `1132b6f6440207173f848eb53ff341029ab9ec0aec59d3734f39d0cc5040a992`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\scripts\run_hamilton.py`: `f3a7d49a9943e5562527188dc93977b1ad5552697a5b6ef2815a541ad2a954ae`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\scripts\hamilton.py`: `935c65527793a6e7299e4194c675d06b4061f9303d87a0052865c08a2b761943`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\logs\hamilton-stdout.log`: `2aa1dd12b404af9cab9fd6089adec4ac35938af65de4a3ea22158ea8fcdc4936`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\logs\hamilton-stderr.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\data\hamilton-resume-execution.json`: `0bece035bea5a0bf2241a2f5eaa3acbab449c837833a758d2fe1f4cffd2fe17d`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\scripts\run_resume.py`: `33d4a89c5d770e37af7eca54f8721331653a8bb3f231c95928abe294ce3feae6`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\scripts\hamilton_resume.py`: `05a8034175cb72a06fc68000deac9455d223694bbb12fd50c56c21746318e823`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\logs\hamilton-resume-stdout.log`: `cb359e18ca81d5f4d0f9878f0b5d07002b41950b9c4da8d2ee06b82281eb621d`
- `E:\Snake-in-a-box\milestones\234-single-colour-exchange\logs\hamilton-resume-stderr.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
