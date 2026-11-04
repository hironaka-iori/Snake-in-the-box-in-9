# Share18 continuation plan

Status: read-only source and saved-evidence assessment. This note is the only file created by this task. No compiler, solver, proof replay, graph computation or process query was run. The selected159 counts are `(3,[6,21],4,3,[6,21])`; the existing broad012034 certificate covers all five counts in `[0,21]`, so it covers that selected case without a new Boolean query.

## Recommended continuation

Keep the exact144 compact CNF, variable meaning table, checked initial tree and checker namespaces. Reuse the accepted144/145/146 objects, and adapt155's streamed proof transport, bounded checkpoint groups and saved-evidence auditor for the remaining share18 replay. Complete the existing104 semantic shards and the actual-snake wrappers separately. This closes the broad012034 share18 theorem and consequently the selected159 context. The count-conditioned012032 share17 theorem is a different result and cannot substitute for any part of this chain.

The old144 batch should not be resumed unchanged. Its `Check1` begins with the repeated-insertion `loadRaw` initialization; its six successful objects precede the stopped check. The direct literal tree and its original-clause truth bridge have since been accepted. Rebuilding that bridge or solving another cap17 query would add work without closing a new logical gap.

## Existing evidence and reusable objects

The independent144 certificate audit records145,215 deductions,14,710,881 propagation references,13,224 original core clauses,2,561,006 derived literal occurrences and at most710 hints in one deduction. The input has96,091 clauses. The native producer's historical status remains `NATIVE_REPLAY_PENDING_HINT_LIMIT`; the later `alternative-review.json` supplies the successful independent replay. These records describe different stages and must remain unchanged.

The saved export preserves the original clause identities and signs, order and multiplicity of literals and hints. Its compact core uses5,779 active proof variables; the semantic map has6,371 variables. The checker offset is8,192, word width14, allocator size14,114 and tree height14. The old export contains2,416 approximately6,000-reference segments and1,324 Lean modules, including104 semantic shards and604 check modules. Its326,828,007 generated source bytes include the older frequent checkpoint design.

Accepted components are:

- Six original144 modules: `LratCheck144`, `LratFast144`, `LocalWindowCnf.ShareWindow144`, and the old `LocalWindowUnsat.ShareWindow144.Data0`, `Data1`, `Data2`. The first three are directly useful. The three old data modules are accepted data, not proof of a replay segment; their initialization and packing must not be combined with the new preorder representation.
- `LiteralData144`, `LiteralSmall144` and `LiteralProbe144`. The full probe checks exactly1,055 deductions and6,006 references from the materialized tree. Only the full probe is needed for continuation.
- `InputTree145` and the28-module chunk package: `ChunkData145`,13 part modules, `ChunkTruthTools145`, and13 fixed part-truth modules. The package proves104 build equalities,104 clause-list equalities,104 slice equalities and104 part truth transfers. Its historical completion record says the final assembly timed out;146 subsequently closes that remaining assembly.
- Three146 modules: `RawChunksAssoc146`, `AssemblyAssoc146`, and `PrefixAssoc146`, with four standard-axiom reports. `AssemblyAssoc146.start_true` has exactly the needed hypothesis `cnfTrue τ ShareWindow144.cnf = true` and concludes truth of `LiteralData144.start`. `PrefixAssoc146.checked_prefix_true` gives truth of `replay LiteralData144.start LiteralProbe144.proof` under that same hypothesis.

The source, object and log hashes of the ten principal accepted objects in the table below were rechecked during this assessment. The complete transitive receipt closure remains a mandatory execution-preparation audit; this note does not claim to have rerun every old auditor.

## Smallest new replay chain

1. **Pin and preserve inputs.** Use the existing compact `certificates/share144.cnf` and `certificates/share144.lrat`, plus `data/share144.json`, the original core-ID table,144 export review and146 bridge receipt. Do not apply the variable renaming twice. Using the compact LRAT is simpler than retranslating the original proof, provided its existing transport audit and exact hash are pinned.
2. **Stream the allocation and packing.** Adapt153's `prepare_replay.py` and `transport_replay.py`; replace all153-specific constants, source paths, theorem namespaces, counts and source hashes explicitly. Retain144's allocator tie order, clause lifetimes and preorder physical-key map from `prepare_raw_init_probe.py`. The old `lr.plan` operates on compact input IDs, while the153 preparer operates on original IDs; this distinction must be resolved explicitly. Compare all first1,055 packed integers against `LiteralProbe144.proof`. Exact equality is the condition for reusing the checked prefix. The initial clauses must occur at the same preorder keys as `LiteralData144.start`; unused keys must have the same tautology meaning.
3. **Verify the transformed full proof before emission.** A new native transport receipt must account for every145,215 deduction and14,710,881 reference, every allocation/reuse and checkpoint, the final empty clause and its final key. The old native proof audit and old packed simulation do not certify a changed physical key map. Stream the105,893,029-byte compact LRAT; avoid loading all hint lists at once. Use the existing14-bit checker only after checking every encoded word fits and the existing per-step fuel accommodates the measured maximum710 hints.
4. **Bridge the accepted prefix to one materialized checkpoint.** Emit a literal checkpoint immediately after deduction1,055. A small new check proves `cpOk (replay LiteralData144.start LiteralProbe144.proof) checkpoint1 = true`. Compose it using the existing `LratFast144.cpOk_true` and `PrefixAssoc146.checked_prefix_true`. This requires a checkpoint-data module, a checkpoint-equality check and its truth consequence. It reuses the accepted prefix theorem and does not repeat the full initial-tree construction or require a new initial-database proof.
5. **Continue only after that pilot passes.** Adapt155's full emitter with `Lrat144`/`LratFast144`, the same `ShareWindow144.cnf`, and the newly accepted checkpoint1. Replay the remaining144,160 deductions and14,704,875 references. Retain the existing segment boundaries: the first continuation group covers original segments1 through31, then32-segment groups, with materialized checkpoints every32 segments and at most four check theorems per check module. Emit the final contradiction as `Unsat ShareWindow144.cnf` in a new159 module. Approximately835 new replay units result from this layout, including the three checkpoint1 bridge units; the generator must derive and verify the exact inventory. No old1324-module inventory or155's137-module count may be retained as an acceptance constant.
6. **Audit exact coverage.** Adapt155's `finish_full_replay.py` to accept the pinned legacy144/145/146 receipt formats as explicit reused dependencies. Check source, object, log, source/checker snapshots, dependency hashes, ordered segment coverage, exact deduction/reference totals, final empty key, final theorem type and permitted axioms. The old144 format is `PASS_WINDOW_REPLAY_MODULE` with `theorem_audits`;145/146 use `PASS` with `axioms`. Do not rewrite old receipts into a new schema or claim they came from the159 checker. The final theorem must have no unproved prefix-truth or contradiction premise.

The proposed32-segment groups follow the completed155 design, whose largest sampled private memory was2,036,826,112 bytes and total compiler time was about1,252seconds for its smaller137-module replay. Those measurements demonstrate that design on155; they do not predict this larger proof's duration or peak memory. If a four-theorem check exceeds its budget, split only the unaccepted group, preserve its failed attempt, and pin a new plan revision.

## Semantic and actual-snake obligations

No `Share144.*-audit.json` receipts are present in144/data. All104 concrete semantic shards remain unaccepted in that package. The full source chain also contains `Share144.Data`, `Structure`, `Compose`, `Sat`, `Refuted`, `Geometry` and `Reversal`, a total of111 target-specific modules. The accepted CNF object is additional and reusable.

Reuse the exact144 semantic data and tags. The core contains167 retained `old/cut` clauses; they must be checked through the generic cut rule and the actual path's local acyclicity. They must not disappear when adapting the lighter import framework. This is different from the six retained cycle exclusions in the012301 semantic package. `Structure` checks counter/totalizer structure; the104 shards check all retained clause meanings; `Sat` assembles satisfiability under the share-cap hypothesis. Finally compose with the new159 contradiction, then check coordinate transport and reversal.

The existing144 geometry source already states the broad desired result: for a fitting six-transition word `(a,b,c,a,d,e)` on five distinct coordinates below9, the five-centre resolution12 share sum is at least18. Its reverse word is `(e,d,a,c,b,a)`. It uses the universal singleton-count bound21 and has no extra parity, endpoint or selected-count premise. Preserve this statement while changing the contradiction import to the completed159 module. A narrow wrapper for `(3,[6,21],4,3,[6,21])` can then specialize the broad theorem; it requires no additional solver query. The reverse-order selected counts would be `([6,21],3,4,[6,21],3)` if stated separately.

A compact input closure is feasible. The imported `LocalWindowModel.olean`, `LocalWindowTags.olean` and `LocalWindowShareModel.olean` hashes in the accepted144 receipts match the copies in147/build exactly. Recommended explicit search order is the new159 build,146/build-independent,145/build-independent,144/experiments/build,144/build-base, then147/build, with148's transfer support and Mathlib added only for modules requiring them. Verify every resolved dependency and its receipt before accepting this order; equal names alone are insufficient. Do not copy the entire older4,162-object semantic overlay. Keep all original objects immutable.

## Resource and acceptance boundaries

Use155's native Win32 memory/process helper, not the old144 CIM monitor. Run one Lean compiler at a time; exclude concurrent graph and TeX work. Preserve its1.5GiB preflight free-memory gate,768MiB runtime floor and3GiB owned-private limit, with the same recorded timeouts and immediate stop on another Lean process. Generic modules use one thread and8,192KiB stack; retain concrete-module settings only where the saved design supports them. Resource query failures must stop safely. A resource stop does not invalidate accepted prior modules and does not authorize a restart from the beginning.

The old `replay-progress-base.json` still contains a historical RUNNING entry. The later `warmup-stop.json` records its intentional memory stop; the stale PID is not evidence of a live task. Do not use that stale progress as a launch or completion gate. Reuse accepted objects only after checking their current hashes and recorded dependencies.

The selected continuation closes a local share premise. Complete replay alone yields a Boolean contradiction; complete semantic interpretation and actual-snake transfer are also required before asserting share18. Even the completed local theorem would leave the other conditional234 premises and complete global certificate obligations. This note claims no new local theorem, graph result or global upper bound.

## Principal reusable object pins

All paths are relative to the repository root. The associated receipt gives the exact source, log and dependency closure.

| Module | Object path | Object SHA-256 | Receipt SHA-256 |
| --- | --- | --- | --- |
| `LratCheck144` | `milestones/144-countfree-share18/build-base/LratCheck144.olean` | `28771cdbe8751e6cad589fd4cc399ac16614804a5360ab36542204e536529b81` | `63650a0e69b04089f78f3ec875e53273fa6375e452ff1ecfda6478532285d2d3` |
| `LratFast144` | `milestones/144-countfree-share18/build-base/LratFast144.olean` | `2e1ead1ac895ba4fdaa3cb469e2a4bc32aa08e34e1dc2e6b23fc0d53b7aeedbd` | `d73eb35cd19542b474ad14638f1a71d9d770395eb505426efbffc4d2c1b63a8e` |
| `LocalWindowCnf.ShareWindow144` | `milestones/144-countfree-share18/build-base/LocalWindowCnf/ShareWindow144.olean` | `eea9ecbff4fd2af878d00d3dc83d0d30aaa5ccd82d65b2652bf46c8508362d17` | `3e49df6b951230145d36a85cdca4bdd0bb77e58da8b81e2b1d685abff1f1ad08` |
| `LiteralData144` | `milestones/144-countfree-share18/experiments/build/LiteralData144.olean` | `de4aff29603d5b44b33c8d94b7918ffc19408aa2828581e2891c1a4e304e1f62` | `546f925b0531e23c7d0a7d0be6597bbf9ab86cfa71b62a2a9c525d36e3c518b2` |
| `LiteralProbe144` | `milestones/144-countfree-share18/experiments/build/LiteralProbe144.olean` | `a92cd45ba125a9031168ba8ea93745200d286ef763f47470f3734894ba2fc3ba` | `1ecc893f432196967ec82193c1494d6cd74637f16a197c555f69073bd7c4a299` |
| `InputTree145` | `milestones/145-countfree-012301/build-independent/InputTree145.olean` | `d46a3358ddb9c805d431bc77ddc2333fc50f64c7acc86780c06fc554e27cbcfc` | `b3df4fcdd1cca85fece752882b819e938feb9f2150dab28d8458ef20c910c2a2` |
| `ChunkTruthTools145` | `milestones/145-countfree-012301/build-independent/ChunkTruthTools145.olean` | `1f1f9addd2095a750dbb3d9f7979867aa3b0a2cd8972dd4d07a8fab335d11a72` | `b40ce5fa628ea6c7572f59958b948787eb6e2108278b52ad7a062d180f249ccd` |
| `RawChunksAssoc146` | `milestones/146-initial-tree-and-paper/build-independent/RawChunksAssoc146.olean` | `8c61b57917dc99a8c50fe3ec136c0eefd74ab4454b8e6b1de57e4eab4864bd87` | `0efe965d546fafb95036ad7766311ba4b4a5fb2625e50c4218b3bf9d88cd463b` |
| `AssemblyAssoc146` | `milestones/146-initial-tree-and-paper/build-independent/AssemblyAssoc146.olean` | `6f4728b3d4639d33f33605d8ecb153bf8348aad2d510a537d329b54ff9466e33` | `c4c03523c0f609e029292d3fa3c91b90a6263ad920e7bdbb33ee257779778d04` |
| `PrefixAssoc146` | `milestones/146-initial-tree-and-paper/build-independent/PrefixAssoc146.olean` | `b82f540836c44add1dcff1d312f93c373195a635c9fe3aafe024d8a33a51c779` | `92338cb19705158bf8a35fb42bd60e00190a95f35bf2c7d72bee398b1cf10678` |

## Input source and evidence hashes

| Path | SHA-256 |
| --- | --- |
| `milestones/144-countfree-share18/data/alternative-review.json` | `475e135176575a00a52dd4dd40c7f50c5f6acf24451ab6c21628dcad855229b3` |
| `milestones/144-countfree-share18/data/export-review.json` | `5e91a9288b3e6c8e067d53b267e8af486fef44d12ee76696a2f7d9bad156df40` |
| `milestones/144-countfree-share18/data/proof-plan-base.json` | `f398fcd7276e16732723e015cd127d2bc372b270912bfa95d68e40c7c866f2ec` |
| `milestones/144-countfree-share18/data/share144.json` | `033ad1a0e1c315dc61e1eb58711d73e87e0cff49fbab2302885a3e6bfb6cdf07` |
| `milestones/144-countfree-share18/certificates/share144.cnf` | `92072a0cde05225d34d0f45e0c69a8c8622c1be1252adc07f62a0357a08e0bb3` |
| `milestones/144-countfree-share18/certificates/share144.lrat` | `74ab1a039d1476e03cfed0500f95f5f27d5935589942c227ff39315d5bd139d9` |
| `milestones/144-countfree-share18/work/certificate-alternative/core-ids.json` | `5aa29ff13ba61e2fdc604339f4a7b78a50279fc6852ef68e156381c119180b77` |
| `milestones/144-countfree-share18/lean/LocalWindowCnf/ShareWindow144.lean` | `1fa19f9fa0fe21ef77240a2572eee3a8dfd8c886cfd8359341415bd59b0320ad` |
| `milestones/144-countfree-share18/lean/LratCheck144.lean` | `09f164a49d9511205d60292c64b1db4509ef34b82c131d0a4ecda8a3977c005b` |
| `milestones/144-countfree-share18/lean/LratFast144.lean` | `f0101d53f2c2651e585f31938e0b5be7b82de49f7ee7c27333b6112116ace56c` |
| `milestones/144-countfree-share18/scripts/prepare_raw_init_probe.py` | `e12a3b7eed2de7c37331f132d0350e50775714fea200f1cbf9fdfd1999522f39` |
| `milestones/144-countfree-share18/experiments/lean/LiteralData144.lean` | `e4143c321f24aab2ef047bf5272bad683db3bc295d39fb785b7a43966fd92ef0` |
| `milestones/144-countfree-share18/experiments/lean/LiteralProbe144.lean` | `b411f3aa2e18f05e4f802fcdd03af0eef27a9f5493592022b0677d6b7aa519e8` |
| `milestones/145-countfree-012301/data/chunked-bridge-completion.json` | `636ce08141dfce6b1824c3274f84979fed223830115f20191ab39a1deae75c7e` |
| `milestones/145-countfree-012301/lean/InputTree145.lean` | `fb0def28d9116c8d93171f68ed82fbc476cb814ccff52ab8d07668c6113cfc37` |
| `milestones/145-countfree-012301/lean/ChunkTruthTools145.lean` | `9d7b1e0fd32acef3a938ff6de73f07e2b1451d214f2bd97e0d36ccf460d235c8` |
| `milestones/146-initial-tree-and-paper/data/bridge-completion.json` | `f9216cdc66e08d605ed96f1d1c6c77fde1a9b771c675be75610cc24c9ba5bee3` |
| `milestones/146-initial-tree-and-paper/lean/AssemblyAssoc146.lean` | `8cb750249fedef668ab9d3a6bafc2fe4a6d53e186e937c237758b6774ba45434` |
| `milestones/146-initial-tree-and-paper/lean/PrefixAssoc146.lean` | `64648d91502fbf309ce606a47115a7a03897a26f8afc9c777494160f76ef9124` |
| `milestones/153-pair-conditioned-share17/replay/prepare_replay.py` | `4415cf458b4d3f387904523d5f614196d4027d471bc86d810e6478a5b084acca` |
| `milestones/153-pair-conditioned-share17/replay/transport_replay.py` | `ba525887f7c634969da399613a51af8b83348936ca21194a949af3fdc4e7fddc` |
| `milestones/155-share17-replay/scripts/emit_full_v2.py` | `83407a0e1526b1c41b4da73f1d9aa6cda0ca09a3b85a8c6c048ff03c1b6df103` |
| `milestones/155-share17-replay/scripts/check_full_replay.py` | `7c6c739aee7bcef0e816d373767e4249f9d4c7fd02af5e9db5e37878fe9b8bbc` |
| `milestones/155-share17-replay/scripts/finish_full_replay.py` | `995d4d7864cc37ba6842823c0534d30659c9cbf32f16ec12372f162d04d9cc06` |
| `milestones/155-share17-replay/scripts/native_resources.py` | `2e9e7d499ef7068d10d7ca7e31c9a9dc7ef19abb72b0396d3eab9824376b4413` |
| `milestones/155-share17-replay/data/full-replay-completion.json` | `d074744dc80ccead20ca771b84a358543a3f7756f0d85a253f03638aa21f3ee6` |
