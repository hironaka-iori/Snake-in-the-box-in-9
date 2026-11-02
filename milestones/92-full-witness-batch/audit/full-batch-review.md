# Full witness batch source review

## Verdict and inspected scope

No unresolved correctness or provenance defect was found in the generated batch. All **127 classes**, **255 generated source files**, **210 base witness lists**, **507 direction-specific jobs**, **791 context keys** and **three history heads** match the pinned materialization, job plan and context-assignment plan. The job data contains **357,820 base entry checks**. Every original full witness order was reconstructed, including the three restored heads.

Snapshot: **2026-11-02T14:10:43.979256+00:00**. This review independently parsed the data and compared all source templates; it ran no compiler, generator or solver. Generated source statements and successful proof receipts are distinguished below.

## Complete data and template comparison

Every generated base witness constructor was read with its family, catalogue index, offset and reversal. Its sequence matches the source witness IDs at the exact class-position slice. Every generated job tuple and every four-field context tuple matches the saved plan in order. All 210 base-list IDs occur exactly once as definitions; the two class 1 definitions are explicit aliases to the existing lists 1 and 3.

All inherited `CoverNNNData` sources match their recorded hashes. Their complete box lists agree with the materialized class geometry order. All 127 original roots agree with the global `recordedClassRoots` literal and the earlier assignment plan. The global key table contains exactly the same 127 per-class lists and all 791 `(direction, history)` pairs; there is no swapped pair order or missing context.

The 124 ordinary newly evaluated class templates are identical after normalizing only their class identifiers. Class 1 differs by its explicit reuse proof and import. Classes 85 and 89 share the checked head-restoration template. Every module carries the expected final membership statement, root/key identities and audit declarations. There are **637 planned class theorem audits** across all generated check modules; this is a planned total, not the number already completed.

The first read-only template comparison incorrectly replaced the numeric substring `000` inside `maxRecDepth 100000`. Restricting normalization to identifier suffixes resolved that audit-script issue. No project source or audit file was changed by the failed attempt.

## Length guards and class 1 reuse

`BatchAssembly.baseJobValid` separately checks that the witness list and box list have equal lengths, that every zipped witness is history-free, and that the optimized validator succeeds at history zero. `baseJobValid_spec` retains all three facts and converts the optimized result to original `entriesValid` through the checked table equality. Thus zip truncation cannot shorten an accepted base job.

Class 1 defines base list 1 as original `witnessList001` and base list 2 as original `witnessList003`. Its six direction assignments remain **1, 3, 307, 308, 310 and 312**, each with 640 entries. `jobs001_valid` changes definitionally to the earlier `class001Jobs.all class001JobValid` statement and invokes its existing theorem. The new module still checks the full context/key/root identities and supplies the batch-facing membership theorem. Its successful receipt confirms that the reuse statement elaborates as intended.

Ordinary classes use the original complete box list. Their context predicate checks the history bound and membership of the exact direction/base-list pair in the checked jobs. It does not silently transfer direction-specific validity to another direction. The final theorem obtains history below 75 from the checked context, preserving the original `numericKeep` predicate throughout.

## The three history heads

Only classes **85 and 89** use `boxesNNN.drop 1` for their bases. Their head is `boxesNNN.getD 0 []`, and each check module proves the full identity `boxesNNN = headBoxNNN :: baseBoxesNNN` before applying the original geometric cover. Consequently the default for an empty head lookup cannot silently substitute an unrelated box.

| Class | Direction | History | Rule index | Base list |
| --- | --- | --- | --- | --- |
| 85 | 177 | 43 | 0 | 146 |
| 85 | 177 | 70 | 2 | 146 |
| 89 | 180 | 68 | 1 | 150 |

Each head is checked separately at its actual direction/history by the original-equivalent optimized validator. The base is transported from history zero. `head_restored_numeric_membership` conses the head before the tail, derives full length equality from tail length equality and supplies the original full ordered cover. No append/reordering step is used. The independently reconstructed full lists agree with original lists 112, 113 and 117 respectively.

The historical rule indices in the ordinary classes are zero placeholders in an unused tuple field. They do not add a history witness or an extra guard to ordinary membership proofs.

## Statement scope

For each class `c`, the generated final theorem assumes `(di,q)` belongs to `recordedClassKeys c`, `code < 46656`, and the original `numericKeep q di code = true`. It concludes acceptance by `retainedDiagram` at `recordedClassRoot c`. The source extracts the original context tuple, rewrites its direction/history by the pair equality, obtains the corresponding checked base job, and applies either ordinary history transport or head restoration.

This is the intended per-class conditional acceptance result. It does not prove that every numerically retained candidate belongs to the union of the context lists. The source-compatible assignment bridge remains a separate theorem. It also does not identify accepted diagram values with exact saved rows, discharge the two reference-refutation catalogues, check endpoint/weight columns or establish a global bound.

## Generator, driver and repaired attempt

`build_batch.py` pins the saved plan, original materialization, earlier class 1 receipts and inherited geometry sources. It checks all generated geometry/witness reconstruction and refuses to overwrite a differing generated source. Current bytes match every entry in `batch-generation.json`.

`check_batch.py` verifies generated inputs and source hashes at startup, checks dependency source/object/log receipts, and reuses a checked module only with the same dependency map. A unique batch lock protects against a second driver. Each fresh proof writes to a unique temporary object, checks unchanged source bytes, compiler success, expected audit count and allowed standard axioms before promotion. Waiting for geometry requires both data and geometric check receipts; the subsequent dependency validation checks their contents rather than accepting file presence alone.

The review identified that a long queue originally had only a startup generation-hash comparison. This has been **addressed**: the current driver compares each dispatched source with `generation['source_sha256']` before either receipt reuse or fresh compilation. The exact earlier checker is preserved as `data/repairs/check-batch-before-dispatch-pin.py.txt`; the added assertion is its only change. Current reviewed sources match the manifest.

The first `BatchContextData` compile failed because it opened `Snake9.Certificate88` without an import providing that namespace. Its source, generator, generation record, log and nonzero-exit record are preserved under `data/repairs/initial-context-import`. The corrected global source differs only by removing that unused namespace from its open statement. All literal contexts and roots are unchanged; all other generated module hashes are unchanged. The subsequent successful data receipt is separate from the preserved failure.

## Observed proof status

At the recorded snapshot:

- `BatchAssembly` had a matching successful receipt with **four** audits.
- `BatchContextData` had compiled successfully, with zero theorem audits.
- Classes **0, 1 and 2** each had matching successful data and check receipts, with **five** audits per check module.
- The restarted pilot run was terminal `PASS_SELECTED_DIRECT_WITNESS_CLASSES` for those selected classes.
- No receipt in this snapshot established completion of all 127 classes. In particular, this source review does not substitute for the future kernel checks of classes 85 and 89.

The earlier failed run retains its old active-module field as diagnostic state; its stopped status does not mean that compiler is still active. Printed audits are inspected under the permitted standard-axiom policy; no blanket zero-axiom claim is made. The inherited dependency closure was not independently rebuilt.

## Exact reviewed hashes

| Source | SHA-256 |
| --- | --- |
| `scripts/build_batch.py` | `cfb21f034ee7200c0e7c2361c798f41ed67dc5da65f623db3b960f7b604ef5d6` |
| `scripts/check_batch.py` | `09490a4ded5026ca1bf64b105a48eaf22ab81d42c4a4402ee141313998c408b6` |
| `lean/BatchAssembly.lean` | `125e73bfd46a00eec888d6d1a3b8d4fcededf409c582edc41affcd394cc470c1` |
| `lean/BatchContextData.lean` | `9bc39b24e6473247d29bbf46d8759cdeb86aae1250533be40dcb8bc87e393394` |
| `lean/Witness000Checks.lean` | `92dcc5141740db9bbf9eee94efa7943c7163dd40b0346f297a4a7b065ed52d8d` |
| `lean/Witness001Checks.lean` | `e6955511bda29524fbb3d44ab5345055af435eb90ed3139d3d136d003ac9570c` |
| `lean/Witness085Checks.lean` | `88a1778aced8b1abddf796a1e0798734c51ea0d87e77ad623b3d8738acb50b27` |
| `lean/Witness089Checks.lean` | `72ca58e626b3c3415a7d0458eb4acbbcc83e0c29b0badd1ca7472dace75cc77f` |
| `data/batch-generation.json` | `892602bf7588099f966a4ceb82d63a1f00d176436ab8b1e24591ae3a2365cc73` |

- Review receipt SHA-256: `46f90634c0951afc37500af01d0c8ff88c05cc0aed784a1cbfd6e456eca3557a`.
- The JSON receipt contains all 255 generated source hashes, inherited input hashes, per-class counts/roots, successful receipt pins, failure snapshots and separately captured run-state hashes.
