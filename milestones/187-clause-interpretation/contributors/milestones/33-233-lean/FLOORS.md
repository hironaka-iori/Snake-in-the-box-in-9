# The floor premise `Floors233`: compatibility with main and port plan

Audit of 10 November 2026. Main was read at commit `32d14f72` (9 November) through the GitHub API (git
trees and blobs by sha), without a branch fetch. Nothing was written to main.

## Port run (10 November): `Floors233` is discharged

**Main's floor modules were compiled on this branch, and `Floors233` is a theorem.** With it,

```
theorem Snake9.Floors233Port.upper_233_of_certs6SB233 (h : LocalWindow.AllRefuted6SB233)
    (hs : LocalWindow.AllRefutedShare6SB233) {m : Nat} (p : Snake m) : m ≤ 233
'Snake9.Floors233Port.floors233' depends on axioms: [propext, Classical.choice, Quot.sound]
'Snake9.Floors233Port.upper_233_of_certs6SB233' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(`outputs/floors233-linux.log`, `# AXIOM AUDIT PASSED`). Its only premises are the certificate
obligations `AllRefuted6SB233` and `AllRefutedShare6SB233`.

**Provenance.** Every fetched source is from origin/main at commit
`32d14f728013acf732c2b6af0b9b341e458769b5`, read through the GitHub API by git blob sha (no git
fetch), and checked against the git blob sha recorded per module in `data/main_floor_modules.json`
(git blob `13cbd759`, sha256 `e0769a76…1d1d`). That file is the provenance record: one entry per module
with its source blob (or archive blob and member), its git blob sha and its imports.

| source on main | blob sha | modules |
|---|---|---:|
| single files (`150/lean`, `152/lean`, `153/lean/LocalWindowCnf`, `154/lean`, `155/lean`, `148/lean`) | one blob each, listed in the manifest | 347 |
| `milestones/151-countfree-replay-pilot/archives/sources151-part00.zip` | `401bab200087334bcdfb3eb172f110c6fc9d4e61` | 339 |
| `milestones/73-countfree-share-catalogue/cases/case7300/data/lean-sources.tar.gz` | `0e046c65e7a5132fd2c9dbbf78222c60058202f9` | 70 |
| `…/cases/case7304/data/lean-sources.tar.gz` | `2ff2cd5e5ba5b23c521c32a2998ae1f7dae9fb0a` | 105 |
| `…/cases/case7306/data/lean-sources.tar.gz` | `bbfdb7ee232ffa23e80c7a16d7ad2cf0aeb8bf57` | 181 |
| this branch: `LocalWindowTagsShare`, `LocalWindowTagsSharePacked` (sources identical to main's, not built before) | `e86deaf6`, `31135692` | 2 |

The 17 other shared modules reuse this branch's existing `.olean` files (13 core, 6 chain).

**How it was run.**

1. `scripts/fetch_main_floors.py ROOT CACHE` wrote the 1,042 fetched sources and the 2 branch copies into a
   project root outside the repository (`/dev/shm/floors233`; the root file system had about 600 MB free,
   which the 0.48 GB of `.olean` files would not fit with a 200 MB margin). It asserts that no fetched module
   shadows a source or `.olean` of this branch. The fetched sources are not in the repository, so no
   `.gitignore` entry is needed; they are regenerable from the manifest.
2. Staleness check before building: `closure()`/`uptodate()` of `work/guarded_lake_build.py` on the port
   root gives 1,044 modules, none of them a branch module (branch modules have no source in the root and are
   leaves). The same check with the core root on the 13 core modules the port imports gives 11 modules in the
   closure and 0 stale. No existing `.olean` of this branch was rebuilt or touched.
3. `nice -n 10 work/guarded_lake_build.py <6 targets> --root /dev/shm/floors233 --direct --trust-mtime
   --no-ilean --jobs 2 --rss-cap-gb 6.5 --min-free-gb 7`, `LEAN_PATH` = core build, chain build, mathlib
   (at most 2 `lean` processes). Result: **1,044/1,044 modules, 0 failed**, 4,157 s wall time
   (plus about 2 min of a first attempt with one job), **8,283 s summed per-module time (2.3 CPU-hours)**.
   The log is `outputs/floors233-port-linux.jsonl`.
   - The 23 LRAT checks of cases 7300/7304/7306 took 1,780 s in all. Peak RSS: 6.24 GB
     (`LocalWindowUnsat.ShareWindow7306.Check1`, 217 s), 4.19 GB (7304 `Check1`), 3.22 GB (7300 `Check1`);
     every other module stayed below 2.9 GB.
   - 1,848 `#print axioms` reports in the build logs, all within `propext`, `Classical.choice`,
     `Quot.sound`; no `declaration uses 'sorry'`; `grep -rlE "sorry|native_decide|^axiom"` over the
     fetched sources prints nothing.
   - `.olean` files: 477 MB (estimate 0.45 GB).
   - `LocalWindowCnf.ShareWindow7304` was finished by a compiler orphaned when the first attempt was
     restarted; it was recompiled to a scratch file afterwards and is byte-identical.
4. The 204 B233 shard sources and the data module were regenerated (`gen_lean_automaton6s.py`, 4 s, into a
   temporary directory), checked with `data/shards6s_B233.sha256`, and placed in `work/final_lean` with the
   old mtime 1793232000, because `chain_audit.py` needs the source of each core module it imports. Their
   `.olean` files had been kept, and nothing was rebuilt.
5. `chain_audit.py --target Floors233Main --reuse --extra-lean-path /dev/shm/floors233-lp
   --log outputs/floors233-linux.log --axioms Snake9.Floors233Port.floors233
   Snake9.Floors233Port.upper_233_of_certs6SB233`. The `--reuse` rule was simulated first: only
   `Floors233Bridge` and `Floors233Main` were stale, and the other 170 chain modules were reused.
   `Floors233Main` took 6 s and 3.11 GB. (A first attempt with the port root itself as the extra path failed
   at the import of `LocalWindowCnf.ShareWindow150`; the log keeps it. See the next point.)
   - The overlay is made by `scripts/floors_overlay.py /dev/shm/floors233/.lake/build/lib/lean /dev/shm/floors233-lp`.
   - `--extra-lean-path` (new) puts prebuilt `.olean` roots first in `LEAN_PATH` and treats their modules as
     leaves. Lean resolves a module in the first `LEAN_PATH` entry that has its top-level directory, and the
     core already has `LocalWindowCnf/` and `LocalWindowUnsat/`. So `/dev/shm/floors233-lp` is a symlink
     overlay: the 1,044 port `.olean` files plus symlinks to the core's 52,405 `.olean` files under those two
     directories (no name collides). The script refuses an extra root that would shadow a core or chain
     `.olean` with a different file.

**Caveat: the port `.olean` files are in tmpfs.** `/dev/shm/floors233` (and the overlay) do not survive a
reboot, and `work/spectral/.verification/chain/Floors233Main.olean` imports them. On a new machine, or after a
reboot, rerun steps 1, 3 and 5 (about 1.2 hours of wall time on 2 cores; 34 MB of network).

**Disk copy (10 November).** After the replay migration of milestone 34 freed disk, the port root was
copied to disk with `cp -a /dev/shm/floors233 /home/user/floors233` (461 MB, 1,044 port `.olean` files;
`diff -rq` against the tmpfs copy prints nothing), and a new overlay was made on disk with
`python3 -I scripts/floors_overlay.py /home/user/floors233/.lake/build/lib/lean /home/user/floors233-lp`
(1,044 port and 42,084 core symlinks, none dangling). Use `--extra-lean-path /home/user/floors233-lp` from
now on; both survive a reboot. The tmpfs copies were left in place. The tmpfs overlay has 10,339 dangling
links to the old `LocalWindowUnsat/<W>/Data*/Check*` files that the migration deleted; Lean never opens
them (no module imports them any more), but a new overlay should be made from the disk copy as above.
Floors233Main was not recompiled against the disk copy (its `.olean` records module names, not paths).

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
- **`work/spectral/stronger/Floors233Main.lean`** (moved from `milestones/33-233-lean/lean/`; compiled
  since the port run above).
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
3. (Done; see "Port run".) Copy `Floors233Bridge.lean` and `work/spectral/stronger/Floors233Main.lean` into the chain build dir and compile them with one
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
