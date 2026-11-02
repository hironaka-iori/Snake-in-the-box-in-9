# Bounded review of case7302 preservation and restoration

Review date: 2026-11-02. Scope: source inspection, metadata consistency, small receipt hashes, path lists and file sizes. No compiler, solver, archive extraction, archive reassembly, or exhaustive archive/member hashing was run. Only this review file was written.

## Finding

The selected proof is covered by the saved source and compact-proof manifests, and its status remains explicitly pending. The original unsliced Lean backup tree is retained locally and omitted from the transport archives. This limitation is now stated explicitly in both READMEs and the pending metadata, as verified in the resolution below. No unresolved defect remains within this bounded review; the remote preservation limit must remain visible. This does not prevent resuming the selected proof.

## Selected proof and pending status

The selected receipt records 389,216 derived clauses, 25,783,817 hints, 27,815 slots, 858 segments, 143 checking modules, and 15-bit encoding. Its input CNF hash and selected LRAT hash agree with the compact-proof archive's member records and the pending checkpoint.

The pending checkpoint records 127 checked modules: 121 clause shards and six data, structure, bridge, composition and satisfiability modules. Their distinct module names equal the successful entries in the pinned semantic/composition records. The saved scope is semantic interpretation with refutation replay still pending. No `proof-audit.json` exists at this inspection. No checked arbitrary-snake share theorem or new global bound follows from these saved progress counts.

The source archive's member/hash dictionary equals the checkpoint's full dictionary of 1,135 selected source files. Its path set equals the current Lean source path set. All 1,005 generated-source fingerprints in the slice-selection receipt agree with the corresponding saved checkpoint entries. All nine small receipt hashes match. This metadata check does not replace verification of all source bytes or archive members.

The slice-selection receipt's phrase “No Lean replay started” describes selection time. The case README and milestone README correctly describe replay as subsequently in progress, while retaining the final theorem as pending. The snapshot script labels process observations historical, records the tool session as execution-context-specific, and warns against starting a duplicate driver. This review did not independently observe or control the running driver.

## Archive sizes and transport

The saved archives are:

| Archive | Bytes | Members | Transport |
| --- | ---: | ---: | --- |
| Selected Lean sources | 106,832,168 | 1,135 | Three ordered parts |
| Original proof evidence | 60,674,063 | 6 | Whole archive |
| Selected compact proof | 43,411,524 | 2 | Whole archive |

The source parts contain 50,331,648, 50,331,648 and 6,168,872 bytes. These sum exactly to 106,832,168, and each is at most 48 MiB. Current archive and part sizes match the metadata. The two other archives are below 100 MiB. The complete selected-source archive remains local.

`split_archives.py` retains the original archive, refuses different existing part bytes, and checks the ordered concatenation hash against the archive hash. `restore_large_archives.py` verifies every part's size and hash, verifies the concatenated hash, and checks any existing complete archive. If reconstruction is needed, it verifies a uniquely named temporary archive before replacing the destination. The destination must resolve inside the case directory.

This review inspected those checks but did not rerun large-file hashing or reassembly. The parent task's restoration verification is a separate execution and its outcome is not assumed here.

## Original Lean backup omission

The original selection manifest references four backup roots containing 1,303 original unsliced Lean files. Those files currently exist locally, and the manifest hash matches the selection receipt. The archive builder collects `backup/original/` and `original-lean-manifest.json`; it does not collect `backup/original-lean/`.

Consequently, the original-proof-evidence archive contains the original CNF, original LRAT, three original JSON receipts, and the Lean manifest, totaling six members. It contains no original unsliced Lean source bytes. `restore_pending.py` cannot recover that original tree from these archives. `verify_saved.py` likewise transports the archive and manifest without the original tree.

If exact preservation of the original generated tree is intended, include that tree in an archive and split it as required. Alternatively, describe the original generated Lean tree explicitly as local-only and reproducible from retained proof inputs. The selected Lean tree and selected compact proof already have full manifest coverage.

## Restore and snapshot safeguards

`restore_pending.py` verifies each archive hash before reading members. It accepts only regular files, rejects links, absolute member names and parent traversal, resolves every destination inside the case directory, rejects duplicate members and unexpected member hashes, and requires exact final member coverage. Existing files must already have the expected hash; different files are not replaced. The original-proof archive restores beneath its recorded backup location, while selected sources and compact proof restore beneath the case root.

The restore scripts are intended for the checked repository manifest. They do not attempt to make the generated manifest an untrusted-input interface. No recursive deletion or movement occurs.

`preserve_pending.py` refuses to issue a partial checkpoint for a case with a completed proof audit. It checks the selected input and export receipt hashes, validates semantic records and source dependencies, and rejects reported proof errors or unsupported printed axioms. Its `--verify` mode also checks compiled objects and logs. Those caches are deliberately excluded from Git, so that mode is a local-cache verification; a fresh host must rebuild the caches before it can pass. Both current READMEs disclose the rebuild requirement.

`snapshot.py` preserves conditional arithmetic and partial-proof boundaries, refuses a completed case, and takes a separate observation of source/object/log-matched successful modules. It does not restart the proof driver. `verify_saved.py` freezes the transport parts, fixed semantic records and logs, case scripts and JSON receipts, current milestone, and handover files. It excludes the live completion record and build caches, while the snapshot stores a separate progress observation. Staged verification checks actual Git blob identities as well as local manifest bytes.

## Fingerprints at inspection

- Slice-selection receipt: `9bd442c56f2fb233101f277c9341fbc9a7397ab8162c49a3bc585b375f40a24e`.
- Pending checkpoint: `1c807517dc3ac174f567988e246d957e287c1c1b9cc89e911aad2252c9b8a203`.
- `preserve_pending.py`: `0f6e33fc741b40007a829e7f52694233a7915b0d26fbd41d0345180a56c637d3`.
- `split_archives.py`: `108f656f3ed4bfb919db0807afa2d3601806f2ccfcba443c083fe4857d0ca05a`.
- `restore_large_archives.py`: `e88394b62889ac65d5bc68e47abc66db2dc73b6dcda241e4c8b54e38cd239515`.
- `restore_pending.py`: `4bf01cc77e57efeba0d315e34e9f01267bd023c0b55f8fe5e63a6c4b0c73a007`.
- `snapshot.py`: `b63590be017acebd6732bbac2b4d5a491fb85c9528fa63269fc81421fa905aae`.
- `verify_saved.py`: `513b95a43d05b7f69807c2485a5e81fab31254efaa87b49907ad820c5b7dafe8`.

## Resolution of the original-tree transport limitation

The parent chose explicit scope rather than an additional archive. Both current READMEs state that all 1,135 selected Lean sources are archived, together with the original compact CNF/LRAT, generation/export metadata, and unsliced-source hash manifest. They identify the superseded 1,303-file unsliced Lean tree as local-only beneath `build/lrat-slice-21fb3e526fcb/original-lean/`, excluded from Git archives. They also state that exact regeneration was not rerun and is unnecessary to resume the selected replay.

The updated `split_archives.py` writes the same distinction to the pending checkpoint's `superseded_original_lean_export` field, deriving the backup location from the selected receipt. The current pending metadata contains that field with the expected location and scope. This resolves the documentation gap without claiming remote preservation or reproduced regeneration of the superseded tree.

A fresh checkout can recover the selected proof sources and compact proof from the stated archives. It cannot recover the exact original unsliced Lean tree solely through `restore_pending.py`; that tree remains local. Compiled caches remain local as already documented. The local theorem is still pending. No archive verification was rerun for this wording check.

Updated fingerprints:

- `milestones/83-012034-share-certificate/README.md`: `a6f142996c082a835ac7fea44744968293d2f03e85057e0c60ef598e4456efa7`.
- `milestones/73-countfree-share-catalogue/cases/case7302/README.md`: `32b93ff7a1a2d98eb7aabfb9a4644c009c24826cdd9746a9ce231b30d5eabe59`.
- `milestones/83-012034-share-certificate/scripts/split_archives.py`: `6d21ee8cc0d8667d1d82519a6f731f2c69bf9e7f1a9c1b732dfd88fb18f5ad56`.
- `milestones/73-countfree-share-catalogue/cases/case7302/data/pending-checkpoint.json`: `02fa9ae44ba28bcceca1642f3dce29c41fb5031e7355ed1e7c4b94cdbfbb4d65`.
