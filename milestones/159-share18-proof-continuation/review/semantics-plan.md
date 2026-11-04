# Semantics continuation for the preserved share-18 proof

Continue the existing universal 012034 share-18 proof with its original source bytes and broad count intervals. This requires less new proof construction than replacing its bounds with the selected interval box. The selected-window statement then follows as a restricted application. No new CNF or solver query is needed for this route.

The source package is prepared: 109 exact original modules are copied under `milestones/159-share18-proof-continuation/lean/`. Every copy matches the generated-source hash in milestone 144's export review. The machine-readable plan is `data/semantic-source-plan.json`, SHA-256 `45a5f1e08e39deb34ef6199fad19e2f1c27fce2a1e8e6fc4de02ad6dba8fd72d`. It identifies 108 modules for compilation and one accepted CNF object for reuse. No compiler was run.

## Remaining proof obligations

The preserved target is `RefutedShare window bounds 12 17`, with canonical directions 012034, window `[0,1,3,7,6,14,30]`, and five broad intervals `[0,21]`. Refuting cap 17 implies integer share at least 18. The following stages remain distinct:

1. Check the exact milestone-144 semantic tables, count/totalizer structure, all 104 semantic shards and their assembly. This must establish that every `AxiomsS` assignment satisfies the exact compact milestone-144 core CNF. It includes ordinary window, degree, endpoint and cycle clauses; count registers; empty-square variables; share thresholds; totalizers; and the share-cap clause. Repeated semantic incidences must remain as encoded.
2. Finish a Lean-checked contradiction for that same core. The independently checked native replay of 145,215 deductions is supporting evidence, not a Lean proof. Milestone 146 connects original core assumptions to the materialized initial tree and the checked 1,055-deduction prefix. It does not complete the contradiction or the concrete semantic interpretation.
3. Compose the core-satisfaction theorem with the contradiction to obtain `RefutedShare`, then instantiate the checked actual-snake frame and share bridge. The fitting window, coordinate relabelling, count bounds and integer-share interpretation must remain explicit.
4. Check reversal and audit the final theorem's sources, objects, dependencies, logs and permitted axioms. A checked prefix or forward source file does not establish the completed two-orientation theorem.

The old `Share144.Geometry` source uses `coreAlpha_le_21` at all five internal centres. Its hypotheses require five distinct coordinates below nine, `r+6<=m`, and directions `(a,b,c,a,d,e)`. It adds no parity or special singleton-count condition. `Share144.Reversal` uses the reversed snake at `m-r-6` and `coreShare_window_rev`. These are prepared source statements; successful checking is still required.

## Exact semantic module order

The package and manifest use this order:

1. `LocalWindowCnf.ShareWindow144`, reused without recompilation.
2. `Share144.Data`.
3. `Share144.Structure`.
4. `Share144.Shard00` through `Share144.Shard99`, then `Share144.Shard100` through `Share144.Shard103`, in numeric order.
5. `Share144.Compose`.
6. `Share144.Sat`.

This is 109 source modules, with 108 on `compile_module_order`. `Refuted`, `Geometry` and `Reversal` are excluded from the current package. The semantic modules do not import the unfinished contradiction.

The accepted CNF receipt is `milestones/144-countfree-share18/data/LocalWindowCnf.ShareWindow144-audit.json`, status `PASS_WINDOW_REPLAY_MODULE`. Its current source and object match the receipt. The reusable object is `milestones/144-countfree-share18/build-base/LocalWindowCnf/ShareWindow144.olean`, hash `eea9ecbff4fd2af878d00d3dc83d0d30aaa5ccd82d65b2652bf46c8508362d17`. Its imported `LocalWindowShareModel` hash exactly matches the checked milestone-147 object. The manifest names the intended local object location; the runner must stage or resolve this exact object without exposing unrelated stale milestone-144 objects. This review did not copy compiled objects.

The runner should resolve fresh milestone-159 outputs first, checked milestone-147 foundation objects next, then the pinned external library paths. The manifest supplies these paths, individual foundation records and their dependency pins. Record actual import resolution before accepting a result.

`Structure` establishes `counts_ok` and `totals_ok`; each shard proves its concrete `ckAllS` test by kernel evaluation. `Compose` supplies the append lemma. `Sat` combines the 104 shards and generic `soundS` into the core-satisfaction theorem. Its long append chain may have different resource requirements from milestone 154's assembly; successful checking is not assumed in advance.

After a complete contradiction for the exact core exists, the existing final order is `Share144.Refuted`, `Share144.Geometry`, then `Share144.Reversal`. The current `Refuted` source imports `LocalWindowUnsat.ShareWindow144`. If a bounded replacement replay uses another theorem name, connect it explicitly to the same core rather than substituting an unrelated `Unsat` result.

## Checked foundation mapping

Use `milestones/147-countfree-clause-semantics/build/<module>.olean` and the corresponding `data/<module>-audit.json` for these six modules. Their current sources and objects matched their accepted receipts in this review. Complete paths, hashes and recorded dependencies are in the source plan.

| Module | Receipt SHA-256 |
| :--- | :--- |
| `LocalWindowModel` | `0579a9d2f73374d814945311bd46335d0f853fa30e0b7e5b41c761123ca5f78a` |
| `LocalWindowTags` | `3b3af52f80497bb26aabaddb8b436002d21a0b6e899f4110cfb7812ace70d153` |
| `LocalWindowTagsPacked` | `53ac282472080d1e526afe903833246da185be39c4bfc0c272b4ed32d5b765bb` |
| `LocalWindowShareModel` | `f09573e5fe8ba0203299e590ff0e2742dc819fbc06108b42b6a8db2a19acfb4e` |
| `LocalWindowTagsShare` | `b9785588e6026d0b8c807543ff63d7af21ccb9386fe6a08928a878e3b322b47b` |
| `LocalWindowTagsSharePacked` | `c635e43b60642f2e2f54411806b9e9b0db636c81c1ad2def22914079700e10ef` |

For eventual actual-window transport, the checked milestone-148 `LocalWindowShareBridge` receipt has hash `9b8e7298a666664f5c1eb486d6598d3766cf7f055ee08aecf51c600dcd88f16c`; its object hash is `bc1273784bee500cbb0620c72365f0696d3d7e7d45571c971b0260eff33e4ebd`. It imports the same milestone-147 share model and milestone-148 direction bridge.

The optional milestone-148 `CanonicalShareAdapter` receipt has hash `cc8d31388c17dbfa640443be4f39c0b3b66c6e61044ff94c69ef56ee44e22f95`; its object hash is `c63a00818911337047f06a1893fecc4c35569c3c797418e543f11c71ee351115`. Its `share_bound_of_either_canonical_match` already handles arbitrary six-direction lists with broad bounds, resolution 12 and cap `K`. Instantiate 012034 and `K=17` once the local refutation is checked. The preserved explicit-coordinate `Geometry` and `Reversal` sources offer another existing interface; a new generic geometric argument is unnecessary.

Retain the actual-window dependency closure recorded in `milestones/148-actual-snake-share-transfer/data/transfer-plan-v4.json` and the corresponding receipts. This bounded review checked selected source/object identities; it did not repeat the full transitive closure audit.

## Reuse from milestones 154 and 155

Milestone 154 demonstrates the separation of concrete clause interpretation from a numerical contradiction. Its generic `canonical_share_bound_with_bounds` and `reversed_share_bound_with_bounds` in `CriticalShareAdapter154.lean` support arbitrary five-count bounds. The accepted adapter receipt hash is `e57fa1ca5a7f0d2f410c579b033be9425b0785b61c27c477b74ade7ee0caf247`; its current object hash is `8430c809c3df79c758ea2d5dc00ff74608db332f69a8edffdcc3522f35c85e07`.

These generic lemmas can transport an established local refutation. They cannot supply the 012034 contradiction. The concrete 154 shards and nine counters concern the different 11,869-clause 012032 core. Milestone 144 has 13,224 core clauses and different semantic data. Neither those shards nor milestone 155's final `share17` theorem can replace the 144 checks.

The checked 147 framework used by 154, the generic 148/154 transport lemmas, and the 155 final-composition and evidence-audit procedure are reusable. New proof of their generic frame invariance, share bridge or reversal identities is not indicated by the inspected sources. Their checked dependency identities must remain pinned.

## Universal proof and selected bounds

The selected canonical bounds are

\[
([3,3],[6,21],[4,4],[3,3],[6,21]).
\]

Finishing the broad proof supplies this restricted conclusion without changing any counter, clause, variable map or replay segment. Regenerating semantic data with these narrower bounds would add new concrete obligations and require an exact core-identity or certificate-transport check. Milestone 154 performed such checks for its own changed interpretation; that success does not establish identity for a new 012034 encoding. No reduction in proof work has been demonstrated by narrowing this existing certificate.

A targeted reversed case would use the intervals in original path order

\[
([6,21],[3,3],[4,4],[6,21],[3,3]).
\]

Stored symbol 6 remains an interval. The eventual local theorem does not by itself complete graph interpretation, the global potential certificate or a new bound for arbitrary snakes.

## Main evidence pins

| Source relative to `E:/Snake-in-a-box` | SHA-256 |
| :--- | :--- |
| `milestones/144-countfree-share18/data/export-review.json` | `5e91a9288b3e6c8e067d53b267e8af486fef44d12ee76696a2f7d9bad156df40` |
| `milestones/146-initial-tree-and-paper/data/bridge-completion.json` | `f9216cdc66e08d605ed96f1d1c6c77fde1a9b771c675be75610cc24c9ba5bee3` |
| `milestones/154-share17-broader-semantics/data/semantics-completion.json` | `e8f3f4a40a6b0f3b26d008daefbed20316f02ce907a455afb6d4ca271c09c87f` |
| `milestones/155-share17-replay/data/actual-snake-completion.json` | `13f9384803807906090cb963f127967a6835d9cc003791968914e6df36caf76b` |

All 109 old and copied source hashes, foundation receipt/source/object hashes and accepted-CNF reuse information are recorded in `data/semantic-source-plan.json`. Old milestone-144, 146 and 147 files were preserved. No pending theorem is marked complete by this package or plan.
