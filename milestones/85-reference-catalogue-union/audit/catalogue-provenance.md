# Reference catalogue source and compiled-object provenance

## Scope and timing

This bounded, read-only investigation searched known local repository and build locations for the reference-catalogue modules and compared selected saved sources and logs against the two pinned Git commits. It ran before milestone 85 rebuilt its two data-only key modules. Those new key-module objects, when checked, supply catalogue data; they do not supply closed refutations of the catalogue entries. This report records the earlier search result and the remaining closed-proof dependency gap separately.

No compiler, solver, fetch, branch change, or case7302 operation was performed. The only subsequent write is this report. No full transitive dependency audit or fresh replay of the historical upper-bound proofs is claimed.

## Search result

Targeted filename searches used `rg --files --hidden --no-ignore` or `rg --files -uuu`, including ignored build files. The search covered all of `E:/Snake-in-a-box`, including milestone build directories, `work/final_lean/.lake`, `work/spectral`, `work/spectral-reproduction`, and `othercontributors`. A second targeted search covered the original `D:/Codex/2026-10-13/new-chat` workspace.

At search time, no `.olean` was found for any of these five modules:

- `UpperBound235`
- `LocalWindowDirGlue6K235`
- `LocalWindowDirKeys6K235`
- `LocalWindowDirUnsatR4`
- `LocalWindowDirKeysR4`

Additional targeted searches found no compiled `LocalWindowDirUnsatR4b` or `LocalWindowDirUnsatK6`, and no compiled `LocalWindowDirGlue6`, `LocalWindowDirKeysR4b`, or `LocalWindowDirKeysK6` in the repository. The `othercontributors` directory contained only `dfs_report.pdf`.

Central-directory inspection of `outputs/research_code.zip` (57 members), `outputs/snake9_lean_project.zip` (32), `outputs/snake9_research_bundle.zip` (51), and `outputs/snake9_spectral_project.zip` (8) found none of the five requested module names. This was a bounded search of the named local locations and archives, not a whole-machine or remote-machine search.

The expanded repository search found these three relevant saved source files:

- `milestones/51-exact-bucket-pressure/data/contributor/UpperBound235.lean`
- `milestones/39-audited-bound-236/upstream/work/final_lean/LocalWindowDirKeysR4.lean`
- `milestones/39-audited-bound-236/upstream/work/final_lean/LocalWindowDirUnsatR4.lean`

## Exact pinned sources and logs

The 235 pin is `74ca83db9c218446211d4f24c5e5a07329fdd847`. The 236 pin is `7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b`. Each row below was compared byte for byte with `git show <pin>:<Git path>` during this investigation and matched.

| Pin | Git path | Local path | SHA-256 |
|---|---|---|---|
| 235 | `work/spectral/stronger/UpperBound235.lean` | `milestones/51-exact-bucket-pressure/data/contributor/UpperBound235.lean` | `420a82ea4368ab222f176ce68d8e014c05c8aeb12bf2a59cd7577ff89c806b80` |
| 235 | `outputs/upper-bound-235-audit-linux.log` | `milestones/51-exact-bucket-pressure/data/contributor/upper-bound-235-audit-linux.log` | `bba097bf8edde534822cae1cb49a6c1afecc290f101771c5620c5fb407eafd87` |
| 235 | `outputs/upper-bound-235-replay-linux.log` | `milestones/51-exact-bucket-pressure/data/contributor/upper-bound-235-replay-linux.log` | `0e843d1cf628d9caadae8f14133b43d2f3197e1816d9d80fb1bff1b207944fe4` |
| 236 | `work/final_lean/LocalWindowDirKeysR4.lean` | `milestones/39-audited-bound-236/upstream/work/final_lean/LocalWindowDirKeysR4.lean` | `0575eddc8a7cd40119326b78e2fd2a8d8e261fa2a7097ef83d0a75eb4c968dd4` |
| 236 | `work/final_lean/LocalWindowDirUnsatR4.lean` | `milestones/39-audited-bound-236/upstream/work/final_lean/LocalWindowDirUnsatR4.lean` | `38a525ccb7dc7c253a0975a63c85c7923f8beb2c92c46d97e44061372ab445cb` |
| 236 | `outputs/upper-bound-236-audit-linux.log` | `milestones/39-audited-bound-236/upstream/outputs/upper-bound-236-audit-linux.log` | `7761a9788eb314aa06e067be858050013605ecfd92461a8b5b6e1aa5a0bc4101` |
| 236 | `outputs/upper-bound-236-replay-linux.log` | `milestones/39-audited-bound-236/upstream/outputs/upper-bound-236-replay-linux.log` | `d716f27b02392117cdd27f68d1d331c6cf220ac9a865cd7b061f3aca4e0d6d87` |

Two further source blobs were read directly from the 235 pin:

| Git path | Bytes | SHA-256 |
|---|---:|---|
| `work/final_lean/LocalWindowDirKeys6K235.lean` | 52,215 | `339171238c9668306822e8619040ed663c4450da784661ed0bdf619bbc389bb7` |
| `work/final_lean/LocalWindowDirGlue6K235.lean` | 5,016 | `e65a7e0ac0ee1a865f35d8db173eaf08b0e3bd9f47dd9215fdf39d94e791806e` |

At the time of the search, these two blobs had no matching expanded source files under the repository. Their later preservation and the data-module builds in milestone 85 are separate work.

The selected 236 source/log package is documented by `milestones/39-audited-bound-236/data/upstream-manifest.json`, which explicitly limits its scope to selected proof interfaces and recorded Linux audits. Its complete dependency sources and replay generators remain associated with the pinned upstream commit.

## Available theorem interfaces and remaining closure gap

`Snake9.LocalWindow.AllRefuted6K235` in the pinned key source is the proposition `AllRefutedList dirKeys6K235`. A definition of this proposition or a checked key-data object does not prove it.

`Snake9.LocalWindow.allRefuted6K235_of_parts` in the pinned glue source has three explicit premises: `AllRefuted237`, `AllRefuted236`, and `AllRefutedK6`. Its finite merge selects 358 entries from `dirKeysR4b`, 294 from `dirKeysR4`, and 635 from `dirKeysK6`, totaling 1,287. These are selected-entry counts, not the full sizes of the first two input catalogues.

`Snake9.allRefuted6K235` in `UpperBound235.lean` closes these premises with:

- `Snake9.LocalWindow.allRefuted237`, imported through `LocalWindowDirUnsatR4b`;
- `Snake9.LocalWindow.allRefuted236`, imported through `LocalWindowDirUnsatR4`;
- `Snake9.LocalWindow.allRefutedK6`, imported through `LocalWindowDirUnsatK6`.

`Snake9.LocalWindow.allRefuted236` is present at line 1482 of the saved `LocalWindowDirUnsatR4.lean`. That source imports `LocalWindowDirSatR4` and 732 Q/R certificate roots, then derives the closed result from `allUnsat236`. The top-level compiled closure object is absent from the searched locations. This investigation did not enumerate or reconstruct every transitive certificate dependency.

Once a matching closed catalogue theorem is imported, `Snake9.LocalWindow.AllRefutedList.mem` supplies individual `Refuted (winOf k.1) (boundsOf k.2)` conclusions for entries with membership proofs. The remaining obstacle is availability and compatible checking of the closed catalogue theorem and its dependencies. The two new data-only key objects do not remove that obstacle.

## Historical checks and present limitation

The pinned 235 audit log ends with `UpperBound235` checked, exit 0, and axiom reports for `Snake9.upper_bound_235` and `Snake9.verified_interval_191_235` containing only `propext`, `Classical.choice`, and `Quot.sound`. Its replay log records a 14,477-module closure for the K6 contribution, 635 new certificate roots, and successful checking of `Snake9.LocalWindow.allRefutedK6`.

The pinned 236 audit log likewise records exit 0 and standard-axiom reports for the upper-bound and interval theorems. Its replay log records a 39,109-module closure, 732 certificate roots, and successful checking of `Snake9.LocalWindow.allRefuted236`.

These are preserved historical Linux check records. They supply evidence of those recorded checks; they do not supply locally importable compiled closed proofs, source-linked object hashes, or a known external local object directory. No fresh local rebuild of either historical closure was performed in this investigation.

The justified next integration is the exact key union/table bridge with its reference-refutation premises explicit. Closing those premises locally requires a compatible replay of the relevant closed catalogue dependencies, or recovery of matching compiled dependencies with adequate provenance. This report establishes no new global snake bound.
