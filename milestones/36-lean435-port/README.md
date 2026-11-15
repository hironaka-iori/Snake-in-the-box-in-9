# Lean 4.35 module port of the certificate stack and the 6SC chain (milestone 36)

Run of 15 November 2026 (branch `research/unconditional-241`). This is the migration chosen after the
spike of [milestone 35, MODULE-SPIKE.md](../35-231-lean/MODULE-SPIKE.md). It sets up a parallel Lean
4.35.0 project in [`lean435/`](../../lean435). Certificates are kernel-checked where they are built. The
final audit imports only interface `.olean` files, pinned by a hash manifest.

**What was left alone.** The 4.19 project, every file under `work/` and `milestones/*/lean`, and every
generator are byte-identical. They are only read. The ported copies are generated into `lean435/src`, which
is not committed. Builds go to a scratch directory (`~/l435`).

## Status

| step | result |
|---|---|
| 1. Core certificate stack as `module`s | **Done.** 86 modules of `work/final_lean`, 23,258 lines: checker v3, all 55 `Lrat*` checker variants, `LocalWindowTags*`, `LocalWindowShareCtx`, the bridges, `Families`, `DirGlue6/7`, `ProofPack`, `NatPack`, `Snake9` (witness section kept), `PathStructure`. Built in 147 CPU-s, peak 3.1 GB (`Snake9`). |
| 2. Mathlib from `/opt/mathlib4-v4.35.0` | **Done.** Only the chain's imports were built: `Mathlib.Tactic`, `Algebra.BigOperators.Fin`, `Data.Fintype.EquivFin`, `Order.Interval.Finset.Fin`. That is 3,135 lake jobs (with batteries, aesop, Qq, plausible, ProofWidgets, LeanSearchClient, importGraph): 6 min for the base part and 33 min for `Mathlib.Tactic`, on 3 cores. `.lake` is 3.7 GB. No errors. |
| 3. Spectral chain | **Done.** The 6S/6SC automaton, bridges, `AggregateDirection6SCConditional`, `CombinedShareToy` and the rest of the closure: 165 modules of `work/spectral[/stronger]`. |
| 4. 6SC toy chain + interface-only audit | **Done.** `Snake9.upper_254_toy6SC : m ≤ 254`, `[propext, Classical.choice, Quot.sound]`. A fresh build of the whole closure is 201 modules, 1,226 CPU-s, 393 s wall on 3 jobs. The audit passes. Bad certificates (`sorry`, `native_decide`, `axiom`) and a swapped interface are all caught. |
| 5. Generator switch | **Done**, by new scripts only. `to435.py` turns generator output into one 4.35 module per certificate. `cert435.py` runs `cert231.py` unchanged, with its records redirected into `lean435/data`. |
| 6. A real certificate of the 232 plan | **Done.** `C70123403A663644K24` (ctx 7) from `certplan231_m232_541_1`: 835,829 replay hints. 4.35 replay **0.67–0.71×** the 4.19 time on the same machine. Details below. |

Reproduce: `bash lean435/tools/toy_audit.sh [DIR]`. It ports, builds as worker, writes the manifest,
publishes, rebuilds the spec layer as auditor, then runs the good audit, the 3 bad certificates and the
swapped interface. The log of the run is in `lean435/toy_audit.log`. Mathlib must have been built first
(see Mathlib).

## Layout

| file | contents |
|---|---|
| `lean435/tools/port.py` | Copies and rewrites 4.19 sources into 4.35 `module` files. The rules are R1–R6 below. It writes the import closure of the targets to `lean435/src` with `PORT-MANIFEST.tsv` (sha256 of every original and every port). |
| `lean435/tools/fixes_extra.py`, `renames_extra.py` | The manual fixes (counted string replacements) and the regex renames. Each carries its reason. |
| `lean435/tools/build.py` | Direct `lean -o` builds in dependency order: ≤ N jobs, `nice -n 10`, an RssAnon watchdog, a disk floor, sha256 stamps, `--keep-going`, and `--lean` for 4.19 comparisons. It writes a jsonl log with wall s, CPU s, peak RssAnon/RSS and the bytes of each output part. |
| `lean435/tools/audit.py` | `manifest` / `publish` (worker side) and `final` (auditor side), described under Audit. |
| `lean435/tools/toy_audit.sh` | The step-4 demonstration. |
| `lean435/tools/to435.py` | Generator switch: Cnf + replay sources become one module per certificate (or `--pair`). |
| `lean435/tools/cert435.py` | Wrapper around `milestones/35-231-lean/certify/cert231.py`. |
| `lean435/tools/closure.py`, `sync.sh` | Import closure over the repository's source roots. `sync.sh` fetches only this branch (see Incidents). |
| `lean435/core-roots.txt` | The roots of the step-1 core set. |
| `lean435/data`, `lean435/cores` | Records and core JSON of the 232-plan certificate(s) made here. |

## Port rules (`port.py`)

- **R1.** `module` goes on the first line.
- **R2: support and chain files.** `import X` becomes `public import X`. `@[expose] public section` is put after
  the header, so every definition is exported with its body (an importer's kernel must unfold them) and
  every theorem with its statement.
- **R3: Cnf modules** (`LocalWindowCnf.*`, `LocalWindowCtxCnf.*`). Only `module` is added. Imports and
  declarations stay private.
- **R4: replay modules** (`LocalWindowUnsat.*`, `LocalWindowCtxUnsat.*`).
  - The Cnf import becomes `import all`. The other imports stay private.
  - `public import LocalWindowShareCtx` is added.
  - One theorem is added, with literal parameters read from the Cnf module's `window`, `bounds`,
    `resolution`, `cap` and `first`:

    ```lean
    public theorem refuted : RefutedShareFrom (winOf …) (…) 12 15 1 := TagsSW.refutedShareFrom_of_sat sat unsat
    ```

    The same scheme gives `RefutedShare …` through `Tags.refutedShare_of_sat` for share keys, and
    `Refuted …` through `Tags.refuted_of_sat` for plain keys.
- **R5.** In support and chain files, imports of certificate modules stay private. The term
  `TagsSW.refutedShareFrom_of_sat N.sat N.unsat` becomes `N.refuted`.
- **R6.** Regex renames for mathlib and core drift, applied to support and chain files:

| rename | count | reason |
|---|---:|---|
| `Finset.card_sdiff h` → `Finset.card_sdiff_of_subset h` | 33 | `card_sdiff` lost its subset hypothesis |
| `Finset.*not_mem*` → `*notMem*` | 12 | mathlib rename (the `List.*` lemmas keep `not_mem`) |
| `dsimp only at h` → `try dsimp only at h` | 14 | `congrArg (fun z => …) he` is now beta-reduced, so `dsimp` "made no progress" (an error) |
| `Finset.filter_card_add_filter_neg_card_eq_card` → `card_filter_add_card_filter_not` | 2 | rename |
| `List.length_eq_zero` → `List.length_eq_zero_iff` | 2 | rename |
| `Nat.add_left_eq_self` → `Nat.add_eq_right` | 1 | rename |
| `f k=localAlpha p ⟨k,hk⟩ := by simp [f,hk]` → `:= dif_pos hk` | 1 | simp now rewrites the `dite` condition `k<m+1` to `k≤m` first |

**Manual fixes** (counted string replacements on the 4.19 text, in `port.py`/`fixes_extra.py`). There are
12, in 9 files:

| module | fix | cause |
|---|---|---|
| `LratV3` | `rw [Option.mem_toList, …] at hy` → `simp only […] at hy` | `Option.mem_toList` now rewrites further |
| `LocalWindowTags` (2) | `Nat.log2.eq_1` → `Nat.log2_def` | `Nat.log2` is now defined by fuel recursion |
| `LocalWindowTags`, `LocalWindowTagsW` | `congr 1` + next line → `try (…)` | `congr 1` now closes the goal |
| `LocalWindowBridge` (3) | `simpa using …` → `simpa [mkPerm]` / `simpa [cnt]` | `simpa` no longer unfolds these definitions |
| `DirectionWindowBridge7`, `DirectionWindowBridge6S` | `simpa [coverHb]` → `simpa [coverHb, CoverH]` (and the `H8` variant) | same: the goal definition must be named |
| `SharedOuterSwitch` | `simpa only [mirror, …]` + `MissingAtNeighbor.mirror` | same |
| `SharedFiniteClassification` (21×) | `simp only [sharedFiniteR] at hcount` before the main simp | see below |

`SharedFiniteClassification` needed a different fix. simp unfolded `ordinaryGoodIndices` before
`sharedFiniteR`. Under `open Classical` that left a decidability instance for the old predicate, and 4.35
no longer matches `Finset.filter_insert` across that mismatch. Unfolding `sharedFiniteR` first restores the
4.19 behaviour. This one was found by a subagent.

Beyond these, the 201-module build gives 537 warnings: deprecations (`if_pos` → `ite_eq_left`, …) and
unused simp arguments. No module prints `declaration uses 'sorry'`. No ported file contains `sorry`,
`native_decide` or `axiom`.

**The 4.35 module system affects proofs in one more way.** The body of an *imported* definition that is
not exposed is opaque, even inside proofs. Core's `Nat.xor` is such a definition. This did not break
anything after the fixes above, but it shows up in error notes ("not unfolded because their definition is
not exposed"). Proofs that relied on unfolding core internals by `rfl` or `decide` may need lemmas
instead.

## Mathlib

`cp -r /opt/mathlib4-v4.35.0 ~/l435/mathlib4`, then `lake env true` fetched the 8 dependencies from
github (15 s), then:

- `taskset -c 0-2 nice -n 10 lake build Mathlib.Algebra.BigOperators.Fin Mathlib.Data.Fintype.EquivFin Mathlib.Order.Interval.Finset.Fin`: 898 jobs, 365 s, 0.97 GB;
- `lake build Mathlib.Tactic`: up to 3,135 jobs in all, 1,957 s, 3.7 GB of `.lake` in all.

Lake 5 has no `-j`. Under `taskset` it ran up to 4 `lean` processes on the 3 allowed cores, each under
0.7 GB. The chain imports `Mathlib.Tactic` in 3 files, which costs about 2,250 more modules than the
other three roots. Narrowing those imports would make mathlib about 3.5 times smaller to build, but
would change the sources. It was not done.

## Audit (`audit.py`, run by `toy_audit.sh`)

**Worker.**

1. `audit.py manifest` writes one json line per module: source sha256, the sha256 and size of `.olean`,
   `.olean.server`, `.olean.private`, `.ir` and `.ir.sig`, the parsed imports and the lean version.
2. `audit.py publish` copies only the public `.olean` of the certificate modules and of the modules
   above them. Each copy is checked against its manifest line.

| published interface | bytes |
|---|---:|
| `LocalWindowCtxUnsat/C70123412A236664K15.olean` | 7,840 |
| `LocalWindowCtxUnsat/C801234032A544643K15.olean` | 8,616 |
| `DirectionWindowBridge6SCToy.olean` | 29,656 |
| `AggregateDirection6SCToy.olean` | 4,152 |

**Auditor** (`audit.py final`).

1. **Rebuild of the spec layer.** The 195 spec and support modules of the closure were rebuilt from
   source into a separate directory (374 s, 3 jobs). All 191 spec modules that the final file loads
   have the same `.olean` sha256 as in the worker manifest. 4.35 output is byte-deterministic.
2. **Hash check** of every interface `.olean` against the manifest.
3. **Clean directory.** A directory of hard links is made, holding exactly the public `.olean` files the
   final file loads.
   - Loaded means: the root's imports, then every import of locally rebuilt modules, but only the
     *exported* imports of worker modules. A worker module's private imports are never loaded by lean.
   - Plus the compiler IR (`.ir`, `.ir.sig`) of the spec layer, mathlib and core. See below.
4. **Final compile.** `lean --setup setup.json Final.lean` runs with `LEAN_PATH=/nonexistent` under
   `strace`. The setup is `importArts` with 3,526 modules.
5. **Whitelist.** `#print axioms` of each listed theorem must be a subset of
   `{propext, Classical.choice, Quot.sound}`. The pass prints AUDIT PASSED, and anything else prints
   AUDIT FAILED with the reasons.

**Results.**

| run | loaded (ours) | result |
|---|---|---|
| `Audit6SC435` (`import AggregateDirection6SCToy`, the 12 `#print axioms` of `build_toy.sh`) | 2 interfaces (aggregate, bridge) + 191 spec + 3,121 mathlib | **PASSED** in 6 s. strace: no file outside the clean directory and the toolchain. Our interfaces opened: `AggregateDirection6SCToy.olean`, `DirectionWindowBridge6SCToy.olean`. The certificates are private imports of the bridge, so **no certificate file of any kind was opened**. `upper_254_toy6SC: [propext, Classical.choice, Quot.sound]` |
| `AuditCerts435` (imports the 2 certificate interfaces, `#print axioms ….refuted`) | 2 interfaces + 14 spec, **`.olean` only, no IR at all** | **PASSED** in 2 s, 16 files (4.7 MB) |
| bad: `ok0 := by sorry` in the ctx-7 replay, rebuilt by the worker with bridge and aggregate | same as the first row | **FAILED**: `upper_254_toy6SC` depends on `sorryAx` |
| bad: `theorem hoff_nd : 0 < 2400 := by native_decide`, used in `unsat` | same | **FAILED**: `…C70123412A236664K15.hoff_nd._native.native_decide.ax_1` |
| bad: `axiom cheat : False`, `ok0 := cheat.elim` | same | **FAILED**: `…C70123412A236664K15.cheat` |
| swapped: the bad bridge `.olean` under the good manifest | — | **FAILED**: `interface DirectionWindowBridge6SCToy.olean: sha256 differs from manifest` |

All three bad certificates sit two levels below the final module (certificate → bridge → aggregate).
The final process sees them only through the bridge's stored axiom list.

**Deviation from "only public `.olean`".** `Mathlib.Tactic` reaches its tactic code through `meta`
imports, and lean then needs the compiler IR of those modules. Without it lean stops with "missing data
file for module ImportGraph.Lean.Syntax", and likewise for core `Lean.Compiler.LCNF.Main`. The audit
therefore lists `.ir`/`.ir.sig` for the **locally rebuilt spec layer, mathlib and the toolchain only**,
never for a worker module, and never any `.olean.private` or `.olean.server`. The IR holds compiled
code, not proofs. The second audit row shows that a final file which does not pull in mathlib's tactics
needs `.olean` alone. For 231, the final module will import the chain, and so mathlib, so expect
the first form.

## Generator switch (step 5)

- **`to435.py --in GENOUT --out SRC NAME…`** reads the Cnf and replay sources that `cert231.py` (or
  `cert233.py`) writes for each certificate and emits **one module per certificate**, as AUDIT-SCALING.md
  wants because of the 65,530 mmap limit:
  - `LocalWindowCtxCert.<N>` for ctx certificates, `LocalWindowCert.<N>` otherwise;
  - all imports private, plus `public import LocalWindowShareCtx`;
  - both bodies, private;
  - the public `refuted` theorem with literal parameters.

  `--pair` gives the two-module form instead.
- **`cert435.py STEP …`** runs `cert231.py` unchanged. It sets `DATA` and `CORE` to `lean435/data` and
  `lean435/cores`, because another agent works in `milestones/35-231-lean/certify`, and its work
  directory to `~/l435/cert231work`.
- **Toy test.** The merged form of `C801234032A544643K15` builds in 41 s at 1.19 GB, against 13 + 24 s for
  the pair. Its public `.olean` is 11,240 B; the `.olean.private` is 0.79 MB.
- The 4.19 generators hard-code CaDiCaL at `/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical`.
  On this machine that path is a symlink to `/usr/local/bin/cadical` (2.1.3), made outside the repository.

## A real certificate of the 232 plan (step 6)

The plan is `milestones/28-combined-identities/data/certplan231_m232_541_1.json.gz`, which has 331 paid
ctx rows. The certificate is `C70123403A663644K24`, ctx 7, chosen at the median of the plan's estimates
(plan 1.62 M hints).

- **Core:** 11,165 clauses, 6,929 variables, 8.3 s.
- **Full proof:** 1,587,540 hints.
- **Replay:** core LRAT 835,829 hints (11.5 s of CaDiCaL), 28,493 lemmas, 16 segments, 4.49 MB of replay
  source.
- **Records:** `lean435/data/*231_certplan231_m232_541_1.jsonl`.

Both toolchains ran on this machine, one `lean` process at `nice -n 10`, on its own core while other
builds used the other cores. The 4.19 run used the same unmodified generator sources and a scratch 4.19
build of the 20-module support stack from the read-only originals. Its `Snake9` copy had the witness
section cut, because it needs more than 4 GB in 4.19 (killed at 4.0 GB after 55 s, as in the spike).
Nothing imports that section. 4.35 builds the full `Snake9` at 3.1 GB.

| module | 4.19.0 CPU s / peak RssAnon | 4.35.0 CPU s / peak RssAnon | ratio |
|---|---|---|---|
| `LocalWindowCtxCnf.C70123403A663644K24` | 40.0 / 0.60 GB | 18.8 / 0.50 GB | 0.47 |
| `LocalWindowCtxUnsat.C70123403A663644K24` (replay), two runs | 142.9, 152.0 / 1.59 GB | 101.8, 102.0 / 1.50 GB | **0.67–0.71** |
| merged `LocalWindowCtxCert.C70123403A663644K24` | — | 125.4 / 1.51 GB (public `.olean` 17,248 B) | 0.65–0.68 of the 4.19 pair |

That is 0.12 ms per replay hint in 4.35 and 0.17–0.18 in 4.19. This confirms the spike's 0.68 on a
second, 4 times larger certificate.

**A second kind of certificate.** A 5-window share key of the same plan was also made:
`T012034A34556K12` (plan 0.59 M hints).

- **Core and replay:** core 6,735 clauses; full proof 388,817 hints; replay 157,569 hints.
- **4.35 build:** as one merged module, `LocalWindowCert.T012034A34556K12`, in 29.3 CPU-s at 1.13 GB.
- **Statement:** `refuted : RefutedShare (winOf [0, 1, 2, 0, 3, 4]) (boundsOf [3, 4, 5, 5, 6]) 12 12`.

Interface-only audit of both 232 certificates (`lean435/audit232.log`):

- The final module imports the two merged modules and prints the axioms of both `refuted` theorems.
- It loads 16 public `.olean` files (4.7 MB, no IR) in 1.8 s.
- Both print `[propext, Classical.choice, Quot.sound]`: AUDIT PASSED.
- The 14 spec modules come from the step-4 auditor rebuild and match this worker build's hashes.

## Production runner `prod435.py` (added after the six steps)

`lean435/tools/prod435.py` is a distributed runner for the paid certificates of a certplan231 plan
(`--help` has the full description).

- **Setup.** Run `prod435.py setup` once per machine. It builds the core stack into `~/l435/prod/core` in
  65 s.
- **Run.** `prod435.py run --plan P --index I --workers W --hours H` has worker I take the certificates
  with `sha1(module) % W == I`, largest first. For each one it does:
  - core, Cnf and replay (`cert231.py` through `cert435.py`);
  - one merged module (`to435.py`);
  - a build against the core;
  - a manifest line.
- **Publication.** It publishes only the public `.olean` files, `manifest.jsonl` and `record.json`,
  fast-forward only, to `refs/heads/xfer/c435/w<I>`.
- **Other commands:** `status`, `merge` (checks every sha256), `free` (the plan's reused keys) and `ctl --stop|--clear`.
- **Test.** 8 certificates of `certplan231_m232_541_1b` were run: ctx 7 ×2, ctx 8, share ×2, plain ×3.
  - Lean CPU per hint was 0.09 (plain), 0.15-0.17 (ctx) and 0.29 (share) ms.
  - Peak RssAnon was ≤ 1.52 GB.
  - The interface-only audit of the 8 merged interfaces passed.
- **Test branches.** The test published to `refs/heads/xfer/c435test/{w0,ctl}` (`PROD435_PFX`). They were
  left in place, since no branch may be deleted in this task.
- **Plain keys** are certified one by one ("every key a seed"). `--seeds FILE` takes a real seed plan
  instead.
- **Free keys:** `lean435/data/free_*.jsonl.gz`.

## Not done, and what the floors would need

- **Floors** (`Floors233`, milestone 33 FLOORS.md; 1,044 modules fetched from main, 2.3 CPU-hours in 4.19
  including 23 LRAT checks of up to 6.24 GB) were not ported. What the port would need:
  1. `fetch_main_floors.py` output as the source root of `port.py`. The roots in `port.py` are a list;
     a `--root` option is the only change.
  2. Rules R1–R4 for the floor certificates. They are `LocalWindowCnf`/`LocalWindowUnsat` pairs with
     older checkers (`LratFast*`, `LratCheckO*`): the step-1 core already ports all 55 of them and they
     build.
  3. Their `refuted` statements are `Refuted`, `RefutedShare` or count-free variants. `port.py` covers
     the first two, and the count-free ones need a third case in `refuted_decl`.
  4. The glue modules (`Floors233Port`) under R2/R5, so certificates become private imports.
  5. A rebuild at about 0.68× of 4.19, roughly 1.6 CPU-hours. The 6.24 GB checks must each run alone.
- **Chain files outside the toy closure.** Only the 201-module toy closure was built. The other files of
  `work/spectral/stronger` (the 233 B233 chain, the 235–238 chains, generated shards) were not.
- **Lake.** Lake was used for mathlib only. Our modules are built by `build.py` with direct `lean` calls, as
  in the spike. Lake on an audit machine that has interfaces but no sources was not tried. `audit.py`
  writes the `--setup` JSON itself.
- **Scale.** The final audit was run with 3,526 import artifacts (772 MB), not with thousands of
  certificate interfaces. Byte determinism was checked on 191 modules within one machine, not across
  machines.

## Incidents

- **A plain `git pull` here fetched every `refs/heads/*`,** including the multi-GB `xfer/*` certificate
  branches. Its temporary pack reached 10.7 GB in 2 minutes. It was killed and the temporary pack deleted
  before the disk filled. `lean435/tools/sync.sh` fetches only this branch. Other agents in this
  repository should not use a plain `git pull` either.
- **Lake ignored the job limit.** Lake started 4 `lean` processes under `taskset -c 0-2`. They stayed on
  3 cores and each used under 0.7 GB.
