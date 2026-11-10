# The floor premise `Floors233`: compatibility with main and port plan

Audit of 10 November 2026. Main was read at commit `32d14f72` (9 November) through the GitHub API (git
trees and blobs by sha), without a branch fetch. Nothing was written to main.

## Verdict

**All five floors are literal: main's theorems prove this branch's copies, with no bridge lemma.**
Every constant the floor statements mention is declared by main in a module that is byte-identical
to this branch's module of the same name, or of which this branch's module is a strict superset
(`Snake9`, `DirectionWindowBridge`). Lean and mathlib are the same versions.

Once main's floor modules are compiled here against this branch's `.olean` files, `Floors233` is
`floors233_of_main share16 canonical7300 canonical7304 canonical7306 share17`. The remaining gap is
exactly "compile main's floor proofs on this branch". That is mechanical but large: 1,042 modules,
about 0.45 GB of `.olean` files, and 2.5 to 3 CPU-hours. Some LRAT checks need more than 3 GB of RSS.

| field of `Floors233` | main theorem | main file | statement | verdict |
|---|---|---|---|---|
| `f012032 : ShareFloor16 [0,1,2,0,3,2]` | `Snake9.ShareTransfer152.share16` | `milestones/152-…/lean/ShareComplete152.lean` | verbatim | literal |
| `f012031 : ShareFloor16 [0,1,2,0,3,1]` | `Snake9.CatalogueIntegration73.canonical7300` | `milestones/73-…/lean/CombinedCatalogue.lean` | verbatim | literal |
| `f012304 : ShareFloor16 [0,1,2,3,0,4]` | `…CatalogueIntegration73.canonical7304` | same | verbatim | literal |
| `f012314 : ShareFloor16 [0,1,2,3,1,4]` | `…CatalogueIntegration73.canonical7306` | same | verbatim | literal |
| `f155 : ShareFloor17` | `Snake9.CriticalShare155.share17` | `milestones/155-…/lean/ShareComplete155.lean` | verbatim | literal |

"Verbatim" was checked mechanically. Each hypothesis of `floors233_of_main` matches main's theorem
statement after whitespace normalisation, with binder names, list spacing and open namespaces kept.

## Definitions: main against this branch

Main's floor proofs were compiled against milestone 148's build. Its module search path is
`148/build`, `147/build`, the milestone's own build dir, and mathlib, according to the `paths` and
`dependencies` fields of main's compile records `logs/*/record.json`. The table compares the sources
of that build with this branch by git blob sha.

| module | declares | main source | this branch | relation |
|---|---|---|---|---|
| `Snake9` | `Vertex`, `Adj`, **`Snake`** | `148/lean-core/Snake9.lean` | `work/final_lean/Snake9.lean` | main's file is a prefix of ours; ours adds only the 191-witness block, and the shared declarations are identical |
| `WindowAutomatonDefs` | **`canon`**, `idx`, `seenAfter` | `148/lean/WindowAutomatonDefs.lean` | `work/spectral/stronger/` | identical (blob `0d32c4e2`) |
| `DirectionWindowBridge` | **`dsOf`**, `symsOf`, `dsOf_rev` | `148/lean-core/DirectionWindowBridge.lean` | `work/spectral/stronger/` | main's file is a subset; ours is `148/lean/DirectionWindowBridge.lean` (blob `8e5ba258`), which adds the 145-key cover. Every main declaration is identical, and only main's 5 `#print axioms` lines differ |
| `LocalWindowBridge` | **`dir`**, `vx`, **`coreAlpha`**, `revSnake` | `148/lean/LocalWindowBridge.lean` | `work/final_lean/` | identical (`5cece23e`) |
| `LocalWindowShareBridge` | **`coreShare`**, `refuted_share_bridge`, `refuted_share_dir` | `148/lean/LocalWindowShareBridge.lean` | `work/final_lean/` | identical (`b6601547`). This is the file main pinned from this branch at `d4936d72` (milestone 35 `upstream.json`, sha256 `8b2d06a6…`) |
| `LocalWindowShareModel` | **`shareLocal`**, `RefutedShare`, the resolution `M` (12 in the floors) | `147/lean/LocalWindowShareModel.lean` | `work/final_lean/` | identical (`b1d0be4b`) |
| `LocalWindowModel`, `LocalWindowDirModel` (`winOf`, `boundsOf`), `LocalWindowDirBridge`, `LocalWindowDirKeys`, `PathStructure`, `WindowAutomatonBridge`, `WindowAutomatonData`, `WindowAutomatonLemmas`, `WindowAutomatonSequence`, `LocalWindowTags*` | support | 147, 148 | `work/final_lean/`, `work/spectral/stronger/` | identical |

- **Toolchain.** Main records Lean 4.19.0 (`commit 6caaee842e94`), the same as `work/final_lean/lean-toolchain`.
- **Mathlib.** The sha256 values of mathlib's `Mathlib/Tactic.lean`, `Mathlib/Tactic/IntervalCases.lean`,
  `lean-toolchain` and `lake-manifest.json` in main's records equal those of `~/lean-deps/mathlib4` at the
  pin `c44e0c8e` (`work/spectral/chain_audit.py`), after converting LF to CRLF. Main builds on Windows.
- **Pinned data object.** Main's 152 note mentions "one pinned historically compiled data object". This is
  `WindowAutomatonData.olean` from main's milestone 32, and its source is identical to this branch's
  `WindowAutomatonData`, which is already built in the chain dir. Nothing needs to be inherited.

## Bridge lemmas written

- **`work/spectral/stronger/Floors233Bridge.lean`** (core Lean, imports `DirectionWindowBridge6S`). It compiled
  in scratch with one `lean -o` (0.5 s), and the log is `outputs/floors233-bridge-linux.log`.
  - `floors233_of_main` takes the five main statements as hypotheses, copied verbatim, and returns
    `Floors233`. The proof is the anonymous constructor, which closes the goal up to delta reduction of
    `ShareFloor16`/`ShareFloor17`.
  - `floors233_fields` is the converse.
  - Axioms: `[propext, Quot.sound]`. These come from the definitions in the statement (`coreShare`, …).
- **`milestones/33-233-lean/lean/Floors233Main.lean`** is a template that is **not yet compiled**.
  - It restates `canonical7300/7304/7306` with main's two-line proofs. They use
    `share_bound_of_either_canonical_match` of `CanonicalShareAdapter` and the case certificates
    `LocalWindow.ShareWindow73xx.refuted`. So the port needs `Share73xx.Reversal` and not the whole
    `CombinedCatalogue`, which would add case 7305 (465 modules), coverage, dispatch and `CountFreeTarget`.
  - It then proves `floors233` and `upper_233_of_certs6SB233 : AllRefuted6SB233 → AllRefutedShare6SB233 → m ≤ 233`.

## Port plan

**Closure.** `data/main_floor_modules.json` lists the import closure of the targets in topological
order: `ShareComplete152`, `ShareComplete155`, `CanonicalShareAdapter` and `Share7300/7304/7306.Reversal`.
It has 1,061 modules and 79 MB of source. Each entry gives its main source (a blob sha, or an archive
blob plus member), its git blob sha and its imports.

| part | modules | source | where the source is on main |
|---|---:|---:|---|
| 012032 replay, milestone 151 (`ReplayUnsat150` and its 342 modules; 339 are new here) | 339 | 35.5 MB | `151/archives/sources151-part00.zip` (the originals are not in git) |
| 012032 semantics, milestone 150 (`Share150.*`, `LocalWindowCnf.ShareWindow150`, `ShareFromCore150`) | 112 | 0.7 MB | `150/lean/` |
| share-17 replay, milestone 155, and semantics, milestones 153 and 154 | 233 | 13.0 MB | `155/lean/`, `154/lean/`, `153/lean/LocalWindowCnf/` |
| cases 7300, 7304 and 7306 of milestone 73 | 356 | 31.6 MB | `73/cases/case73xx/data/lean-sources.tar.gz` (the `Check`/`Data` modules are not in git as files) |
| 148 and 147 adapters (`CanonicalShareAdapter`, `ShareComplete152`, …) | 2 | small | `148/lean/`, `152/lean/` |
| identical to this branch (reused `.olean` files; `LocalWindowTagsShare` and `…Packed` are built from this branch's sources) | 19 | | |

**Can main's modules be imported as-is?** Yes, as sources. Main's `.olean` files are not in git and were
built on Windows, so every module is recompiled here.

- **Module names.** None of the 1,042 new module paths exists in this branch's core or chain roots. The
  19 shared names are identical modules.
- **Declarations.** A namespace-aware scan of all 1,061 sources and of this branch's 233-chain closure
  (183 modules) finds no declaration declared twice. So one module can import main's three closures and
  `AggregateDirection6SB233` together.
- **The two `CanonicalShareAdapter` copies.** Main has two, `148/lean` (imports `Mathlib.Tactic.IntervalCases`)
  and `73/adapter/lean` (imports `Mathlib.Tactic`). Their declarations are identical. The manifest uses 148's
  copy. Only the two 15x adapters and the template import it, and the 73 case modules import `Mathlib.Tactic`
  themselves.

**Measured here.** Script `scripts/port_main_floors.py`, one `lean -o` at a time, `nice -n 10`. Logs:
`outputs/floors-port-pilot-linux.log`.

- **Prefix of the 012032 replay.** 21 modules, up to `ReplayCheck150_00000`: 112 s in all. Per module,
  `ReplayParts` took 5 to 8 s, the first `ReplayCheck` 15.5 s and 0.90 GB. Main's receipts for the same
  modules are 10.3 and 13.5 s, so main's per-module times carry over. The script's axiom check passed on every
  report these modules printed: each names only `propext`, `Classical.choice` or `Quot.sound`.
- **Case 7300.**
  - 55 of its 70 new modules built: the semantics (41 shards, `Data`, `Structure`, `Compose` and `Sat`;
    `Compose` and `Sat` import mathlib, 2.5 GB RSS), the CNF, the LRAT checker and the 7 data modules
    of the first check.
  - The first LRAT check, `LocalWindowUnsat.ShareWindow7300.Check1` (6 `decide +kernel` segments),
    **reached the 3 GB RSS cap after 85 s and was stopped**. Main checked it under a 3 GiB private-bytes
    cap on Windows. Here it needs a higher cap, such as the 6.5 GB that `handoff/PROMPT.md` uses for
    replay checks.
- **`.olean` sizes.** The sizes are far larger than the sources:
  - `LocalWindowCnf.ShareWindow7300`: 95 kB of source gave a 14.4 MB `.olean`;
  - `ReplayParts`: about 30 times the source;
  - `Share73xx.Data`: about 28 times;
  - checkpoints: about 5 times;
  - replay data: about 1.1 times.

**Estimates for the whole port.**

| resource | estimate | basis |
|---|---|---|
| CPU | 2.5 to 3 hours, single process | main's receipts: 0.90 h for the 342 replay modules of 152, 0.70 h for the 138 of 155, 0.11 h for each semantics set. The 23 LRAT checks of cases 7300/7304/7306 take about 2 min each, and their data and shards about 10 min |
| disk | about 0.45 GB of `.olean` (±30%), plus one source at a time with `--delete-sources`, plus 21 MB of archives | the measured ratios per module kind. The largest items are the 5 `LocalWindowCnf` modules (about 140 MB), `ReplayParts` (about 80 MB) and checkpoints (about 65 MB) |
| RAM | 0.5 to 0.9 GB for the replay modules; 2.5 GB for the mathlib modules; more than 3 GB for the milestone-73 LRAT checks | pilot |
| network | about 34 MB | the 4 archives (21 MB) and 347 single sources (13 MB) |

**Steps.**

1. Free about 0.7 GB of disk. The current free space (about 0.3 GB) does not fit the port. Choose a
   build dir outside the repository, for example on a larger volume.
2. Run `python3 milestones/33-233-lean/scripts/port_main_floors.py --build-dir B --delete-sources --max-rss-gb 6.5 --log L`.
   - The script fetches each source by blob sha and checks its git blob sha.
   - It compiles in manifest order with `LEAN_PATH` = B, the core build dir, the chain build dir, then mathlib.
   - It stops on a failure, on `sorry`, or on a non-standard axiom report.
   - It is resumable, because a module whose `.olean` exists is skipped.
   - `--only ShareComplete152` (or `ShareComplete155`, `Share7306.Reversal`) builds one floor at a time.
3. Copy `Floors233Bridge.lean` and `lean/Floors233Main.lean` into the chain build dir and compile them with one
   `lean -o` each. `LEAN_PATH` is the same plus the mathlib packages. The B233 chain `.olean` files
   (`AggregateDirection6SB233` and the modules it imports) must be present; the 204 shards were deleted after
   the production audit and must be regenerated, which takes about 0.7 CPU-hours (README, "Production build").
4. Audit: `#print axioms Snake9.Floors233Port.upper_233_of_certs6SB233` must print only `propext`,
   `Classical.choice` and `Quot.sound`. `grep -lE "sorry|native_decide|^axiom"` over B must print nothing;
   the declaration scan found no `axiom`.
5. What then remains for an unconditional 233 is the certificate obligations `AllRefuted6SB233` and
   `AllRefutedShare6SB233` (README, "Remaining work").

**Cheaper alternatives, not taken.**

- **Main's `.olean` files.** Importing them would need main's Windows build dirs, which are not
  published. Version-wise they would be loadable, since the `.olean` format is platform-independent
  for the same Lean.
- **Dropping a floor.** The plan already builds only what the five floors need: `ShareComplete152`,
  `ShareComplete155` and the three 73 cases. Dropping a floor would lower share fields of the B233 set,
  so the chain would have to be solved again.
