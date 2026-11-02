# Reference shape cache pilot review

## Verdict and snapshot

No concrete metadata, request, ordering, guard or conclusion defect was found. The six original direction/list jobs, both 640-entry witness lists, every reference cache request and the final theorem statement agree with milestone 90 and the pinned materialization/job plan. The direct baseline source is byte-identical to milestone 90 `Class001WitnessChecks.lean`.

Snapshot: **2026-11-02T13:51:08.933741+00:00**. All four proof trials had successful immutable receipts at that snapshot. This review launched no compiler, solver, generator or benchmark. Mutable run state was recorded separately from immutable source/receipt/log hashes.

## Complete cache and list comparison

An independent recursive-descent parser consumed the complete balanced shape literal. It contains **156 distinct leaves**, correct stored left leaf counts and maximum depth **8**, and agrees exactly with `cache-pilot.json.gz`. The generated `pilotIndices` case split selects the matching six index lists and defaults to an empty list outside those directions.

Each job has **640 entries**, including **622 reference requests**, **26 distinct descriptors** and 18 nonreference entries. All **3,732 reference requests** use exactly the **156** stored descriptors, each of which is used. The **108 nonreference entries** retain the original compatibility calculation and ignore their zero placeholder cache index.

Every request was independently reconstructed as `(direction, offset+2, symbolLength+1, reverse, canonicalPattern)`. Its index is below 156 and its complete descriptor equals both the saved entry and the actual balanced-table lookup. All 156 shapes were checked directly against their direction words. Each reference singleton condition agrees with the relevant coordinates of the original entry's box. Both witness lists were parsed constructor by constructor, including indices, offsets and orientation.

| Direction | Original list | Plan job | Entries | Reference requests |
| --- | --- | --- | --- | --- |
| 1 | 1 | 1 | 640 | 622 |
| 3 | 3 | 3 | 640 | 622 |
| 307 | 3 | 309 | 640 | 622 |
| 308 | 3 | 310 | 640 | 622 |
| 310 | 1 | 312 | 640 | 622 |
| 312 | 3 | 314 | 640 | 622 |

`pilotCountLists` contains exactly lists 1 and 3. Their order and all box coordinates agree with the original class 1 geometry. Although the count-list predicate operates on a zip, the final job check separately proves that witness length equals box length. Cached compatibility also checks index-list length equals entry-list length. Both zips therefore preserve the complete intended job in the final argument.

The first read-only audit attempt incorrectly indexed the outer list of boxes in an additional singleton check. The audit expression was corrected to select the current entry's box before its coordinate. The complete comparison then passed. That audit-code error changed no project source or artifact and is recorded in the receipt.

## Soundness and defaults

`cachedCompatibilityAt` replaces only a reference shape evaluation. It retains history/direction bounds, reference catalogue bounds, minimum symbol length and placement limits. It additionally requires a bounded cache index and equality to the complete `referenceRequest`. Count values are checked independently by the count factor.

`cachedCompatibility_sound` uses validity of every index below `shapeCount` and the checked descriptor equality to recover the original shape condition. Nonreference constructors use unchanged compatibility, including the original history `extensions.idxOf` operation. Box length, count tests and all defaults remain in the checked factorization.

This is a soundness implication. It does not claim that an arbitrary incomplete cache accepts every originally compatible witness. The concrete proof checks shape validity on every actual `pilotShapeAt` result and exact correspondence for every request. It therefore does not require an unproved flattening identity for the cache tree. Its default shape cannot equal a guarded reference request, whose requested width is at least three while the default width is zero. The audit independently checked the table ordering as well.

`entriesCachedCompatibility_sound` uses its length condition to recover every original entry. `entries_valid_of_cache` combines compatibility with the count factor. The concrete proof establishes membership of each witness list in the two checked count lists, allowing count-list reuse while retaining six direction-specific compatibility checks.

After changing only the theorem name, the cached theorem's complete hypothesis/conclusion header is identical to milestone 90's: membership of `(di,ws)` in the six jobs, any `q < 75`, `code < 46656`, and original `numericKeep q di code = true` imply acceptance by `retainedDiagram` at `root001`. It invokes the same history-free transport and `originalCover001`. There is no claim of arbitrary history compatibility, exact saved-block equality, whole-array coverage or a global snake bound.

## Receipts and benchmark

The generic `ShapeCache` receipt has three printed audits. Both cached trials have five audits and both direct trials have two. Immutable trial receipts match current sources and their immutable logs. Their recorded object hashes identify completed objects, which later deliberate trials may replace. The transitive dependency closure was not rebuilt.

The finite pilot assertions are **not axiom-free** despite using `decide +kernel`. Shape validity and cached/direct job validity list `propext` and `Quot.sound`; the count-list result lists `propext`; final membership also lists `Classical.choice`. All recorded axioms belong to the permitted standard set. No `sorryAx` is present.

| Trial order | Module | Recorded seconds |
| --- | --- | --- |
| 0 | `CachePilotData` | 45.219 |
| 1 | `DirectPilotChecks` | 18.812 |
| 2 | `CachePilotChecks` | 24.203 |
| 3 | `CachePilotChecks` | 28.016 |
| 4 | `DirectPilotChecks` | 37.875 |

The proof order is direct, cached, cached, direct after separate data compilation. Each trial starts a fresh compiler and includes imports, elaboration, kernel checking and object emission. The cached time includes all 156 shape checks, both count lists, every descriptor correspondence and index guard, list lengths, history-free/list-membership checks, and final original-validator/numeric-membership assembly. It measures the complete named cache proof module.

The proof trial excludes Python descriptor/index generation, earlier generic `WitnessFactors` and `ShapeCache` compilation, separate `CachePilotData` compilation and compilation of existing shared dependencies. `ShapeCache` took **46.125 seconds** separately; `CachePilotData` took **45.219 seconds**. These costs must be included when discussing end-to-end effort, even when treated as amortizable setup.

Before each trial the saved inventory showed three Python processes, two Lake processes and two Lean processes. This is a snapshot before the timed launch, not a measurement of CPU, memory or I/O activity throughout the run. Background load was not isolated or quantitatively matched. The driver preserves immutable trial records, previous observations and a source-before/source-after equality check.

Direct times were **18.812 and 37.875 seconds**, differing by more than a factor of two. Cached times were **24.203 and 28.016 seconds**. The small sample averages do not support a reliable speedup conclusion under this variation. The justified result is successful theorem-preserving reuse with an inconclusive timing comparison. Repeated checks add timing observations, not new distinct theorems.

## Exact reviewed hashes

| Source | SHA-256 |
| --- | --- |
| `lean/ShapeCache.lean` | `dbd327af548176318b2e726884a08d8ce7ef2738e6b494f03de8b2a8d44b2592` |
| `lean/CachePilotData.lean` | `9e10c9e8ed38b5d56526a2a8d2edaa8d33cbfb17363a2336b18323a9af5a25e9` |
| `lean/CachePilotChecks.lean` | `a3ba79db8d0cfb4bed4a025cbd6d4c0d49d49d1b9455d763543bd472f3252ca6` |
| `lean/DirectPilotChecks.lean` | `e377af490b0bd03f0666b480df3a6dd71417ac9529bb479d776ec1d070bb2cab` |
| `scripts/build_pilot.py` | `ce0dc21ce9441f7fd0482125c8082b6fc32d262ffbd0f6d0c4978c4430b7bb72` |
| `scripts/check_pilot.py` | `082c233dd734f2b3c9b7650974d9c7ac1cdcb5358190cfa4cfc0b6c2ceaaa694` |
| `data/pilot-generation.json` | `4681516989be64344df612a0e32aafeffd896810627f22948079edb1a73629e6` |
| `data/cache-pilot.json.gz` | `a2cc1c992cf8c1d489e634491350769d3bf45b887953e19f140ffe03830cafcc` |

- Review receipt SHA-256: `1304d54a4bf3a9bbe4a9648c417e35a9537275e6adedcd93fd7b640bdf84c208`.
- The JSON receipt includes immutable trial receipt/log hashes, stable dependency source/object/log hashes, complete cache usage counts and separately hashed run-state snapshots.
