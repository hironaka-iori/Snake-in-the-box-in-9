# Floors in Lean 4.35: `Snake9.Floors233Port.floors233`

Run of 15 November 2026 (branch `research/unconditional-241`, environment `snake-in-the-box-9-lean435`,
4 cores, Lean 4.35.0). It ports the floor premise of `milestones/33-233-lean/FLOORS.md` from the
4.19 build to 4.35 `module` files.

## Result

```
public theorem Snake9.Floors233Port.floors233 : DirectionWindow6S.Floors233
'Snake9.Floors233Port.floors233' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **Statement.** `Floors233` is unchanged: it comes from `Floors233Bridge`, ported by the port lead's
  `port.py`.
- **Module system.** Every one of the 1,070 modules is a `module`.
- **Checks.** No `sorry`, no `native_decide`, no `axiom` in the sources. There are 1,897 `#print axioms`
  reports in the build logs, all within the whitelist.
- **Data boundary.** A module that imports `Floors233Port` opens only the 24 interfaces of the
  `Floors233Bridge` support closure (strace). It opens **none** of the 1,046 floor modules. The
  restated `audit_floors : Floors233 := floors233` prints the same three axioms.
- **Not in this module:** `upper_233_of_certs6SB233` from `Floors233Main`. It needs the 233 chain
  (`AggregateDirection6SB233`), which belongs to the chain port.

## Provenance

| step | tool | record |
|---|---|---|
| fetch | `floors/tools/fetch.py ORIG CACHE` | `floors/data/FETCH-MANIFEST.tsv` |
| port | `floors/tools/port_floors.py ORIG SRC` | `floors/data/FLOORS-PORT-MANIFEST.tsv` (sha256 of each original and each port) |
| build | `floors/tools/buildk.py` | `floors/data/OLEAN-MANIFEST.tsv` (sha256 of each source and of every output part) |
| audit | `floors/tools/audit_floors.sh SRC BUILD` | checks 1-4 of its header |

**Fetch.** 1,042 main modules come from origin/main at `32d14f72` through the GitHub API, by blob sha.
- 347 are single blobs; 695 are members of the 4 archives, which are themselves fetched by blob sha.
- Each is checked against the git blob sha of `milestones/33-233-lean/data/main_floor_modules.json`.

The 19 branch modules are this branch's files, checked against the same manifest. The exceptions are
`Snake9` and `DirectionWindowBridge`: this branch's files are strict supersets of main's `lean-core`
copies (FLOORS.md, "Definitions"). The 4.19 port run used them too.

**Ported sources are not committed.** They are regenerable in about 30 s from the manifest and the
rewriter (83 MB). The output hashes are committed instead. 4.35 output is byte-deterministic: 4
modules (replay check, shard, `ShareComplete152`, `Floors233Port`) rebuilt to identical `.olean`
and `.olean.private` files.

## Port rules

- **Port lead's modules.** The closure of `Floors233Bridge` plus the 19 branch modules (27 modules) go
  through the port lead's `lean435/tools/port.py`, unedited, run with `--out SRC`. That covers rules
  R1/R2, its fix table and its renames.
- **Rule F1, main modules.** The 1,042 main modules get:
  - `module` on the first line;
  - every `import` made a `public import`;
  - `@[expose] public section` after the header.
- **Why F1 exposes data.** Inside the floor closure the data must stay unfoldable. `decide +kernel` and
  `rfl` in the check, truth and replay modules reduce definitions of other modules, as in 4.19.
- **Where data is hidden.** The interface boundary is `floors/src/Floors233Port.lean`. It imports the
  five floor modules privately: `CanonicalShareAdapter`, `ShareComplete152`, `ShareComplete155` and
  `Share73xx.Reversal`.
- **Fix table.** `floors/tools/fixes_floors.py` is applied by exact match with a count. A fix on the
  port lead's output is skipped only when `port.py` already repairs that spot; 4 are skipped this way,
  in `WindowAutomatonBridge`, `DirectionWindowBridge7` and `DirectionWindowBridge6S`.

## Manual fixes (22 applied)

| module | original | 4.35 | reason |
|---|---|---|---|
| `CanonicalShareAdapter` | `import Mathlib.Tactic.IntervalCases` | removed | no mathlib (below) |
| `Share7300/7304/7306.Compose`, `.Geometry` (6) | `import Mathlib.Tactic` | removed | same |
| `CanonicalShareAdapter` l.76, `Share73xx.Geometry` l.30 (4) | `interval_cases i <;> …` | `rcases (show i = 0 ∨ … ∨ i = 4 by omega) with rfl \| … <;> …` | `interval_cases` is mathlib; core case split, same goals in the same order |
| `Share73xx.Geometry` l.18 (3) | `interval_cases j` (then 6 bullets) | `rcases (show j = 0 ∨ … ∨ j = 5 by omega) with rfl \| …` | same |
| `Share73xx.Reversal` l.15 (3) | `interval_cases j <;> rfl` | `rcases (… j = 5 by omega) … <;> rfl` | same |
| `CriticalShareAdapter154` l.120, l.126 (1 entry, 2 sites) | `interval_cases i <;> simp […]` | `rcases (show … by first \| omega \| (simp at hi; omega)) … <;> simp […]` | same (`hi : i < [..].length`) |
| `ReplayRawChunks150`, `ReplayRawChunks153` (2) | `simpa only [… List.all_map, …]` | `… List.all_map, Function.comp_def, …` | `List.all_map` now produces `f ∘ g` |
| `ShareFromCore150` l.19 | `simpa only […, winOf, broadBounds] using …` | first `rw [show winOf [0,1,2,0,3,2] = [0,1,3,7,6,14,10] by decide +kernel, show broadBounds = [(0,21),…] from rfl]` | `winOf` reduces through `Nat.xor`, which 4.35 core does not expose to `simp`; `simp only [broadBounds]` stops at `List.replicate` |
| `CriticalShareAdapter154` l.115 | `simpa only […, winOf] using …` | the same `rw [show winOf … by decide +kernel]` first | same |
| `WindowAutomatonBridge` l.187, l.205 (2) | `Nat.add_left_eq_self`, `List.length_eq_zero` | `Nat.add_eq_right`, `List.length_eq_zero_iff` | renamed; now also in `port.py` (superseded) |
| `DirectionWindowBridge7` l.179, `DirectionWindowBridge6S` l.402 | `simpa [coverHb] using h` | `simpa [coverHb, CoverH] using h` | `simpa` no longer unfolds the goal `def`; now also in the port lead's `fixes_extra.py` (superseded) |

Every replaced proof is kernel-checked by the build, and every module prints its axioms.

**No floor module needs mathlib.** The only mathlib use was `interval_cases`, in 7 files. The mathlib
dependency repositories could not be downloaded from here: codeload.github.com returned 403. The port
lead built mathlib in the same environment with lake over git.

## Build

- **How.** Direct `lean -o` per module with `buildk.py`, a copy of the port lead's `build.py` with
  `--keep-going` and `--big-rx`: 3 jobs, 4.5 GB cap. The 23 LRAT checks ran alone each, with a 9 GB cap.
- **Passes.**
  - **First pass:** 1,055 of 1,070 modules compiled with no change beyond F1 / `port.py`; 2 failed; 13
    were not started because an import failed.
  - **Later passes:** 3 more failures, then 1 more, all fixed as in the table.
  - **Final run:** 1,070/1,070 up to date.
- **Time.** About 50 min wall in all. **1.73 CPU-hours** summed over the successful compiles, against
  2.3 in 4.19. The 23 LRAT checks took 1,501 s, against 1,780 s in 4.19.
- **Peak RssAnon.**

  | module | 4.35 | 4.19 |
  |---|---:|---:|
  | `LocalWindowUnsat.ShareWindow7306.Check1` | 5.09 GB | 6.24 GB |
  | `…7304.Check1` | 3.25 GB | 4.19 GB |
  | `Snake9` (witness block) | 3.11 GB | — |
  | `…7300.Check1` | 2.46 GB | 3.22 GB |

  Everything else stayed at 2.3 GB or below.
- **Outputs.**

  | part | size |
  |---|---:|
  | `.olean` | 198 MB |
  | `.olean.private` | 352 MB |
  | `.ir` | 66 MB |
  | total | 642 MB |

  The build lives outside the repository, in `/home/user/f435/build`, and is not committed.

## Not verified

- **Temporary copies of shared modules.** The 27 core/chain modules (`Floors233Bridge` closure + 19
  branch modules) were ported here into the floor tree with the port lead's `port.py`. The port lead's
  `~/l435/prod/core` build was not used. When the chain port uses its own build of these modules, the
  floors must be rebuilt against it, or the `.olean` hashes of the shared modules compared (both trees
  run the same `port.py`; check that its version matches).
- **No `leanchecker` run.** It was not run on the floor modules, and no independent kernel re-check was
  done.
- **No interface-only `--setup` run.** The audit used plain `lean` with `LEAN_PATH`, which also opens the
  `.server`/`.private` parts of the 24 loaded modules. It did not list only public `.olean` files the
  way the spike did. strace shows that no floor module is opened at all.
- **One machine only.** Determinism was checked on 4 modules on this machine.
