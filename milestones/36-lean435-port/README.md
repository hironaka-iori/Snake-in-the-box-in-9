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
- **Big jobs of the 231 plan (`certplan231_563_1_cap`).** 62 paid certificates are above 30 M plan hints
  (2.53 G hints in all), 23 above 40 M (1.20 G) and 20 above 47 M (1.07 G).
  - The largest, `T012345A44456K29` (share, 57.7 M plan hints), was run end to end with `--no-sync`. It
    gave 51.4 M replay hints, cores 428 s, an LRAT search of 4,065 s and a Lean build of 19,039 CPU-s
    (0.37 ms/hint), 6.6 h in all.
  - Peak RssAnon was 9.06 GB (VmHWM 9.86 GB). That fits the default 13 GB cap, so no plan change is
    needed.
  - `predict_gb` is now 1.9 + 0.14 GB per M plan hints (was 1.2 + 0.25), so such a job no longer
    reserves the whole 12 GB budget.
- **Work stealing.** `run --steal --index J` is a helper: it takes the plan's unpublished, unclaimed items
  smallest first and publishes to `xfer/c435help/w<J>`.
  - Owners and helpers scan every `w*` branch of `c435` and `c435help` (manifest and record blobs only,
    by partial fetch: 29 s the first time on 32 branches, then 2 s; 1.7 MB) and skip what is published.
  - Claims: one ref per machine with a single writer, `xfer/c435claim/o<I>` and `xfer/c435claim/h<J>`;
    readers take the union. (The first version's single compare-and-swap ref `xfer/c435help/claims`
    failed under contention and is no longer used.) Ties: the earlier claim wins; within 5 s, owners
    before helpers, then the lower index. A claimant waits 15 s after its write before reading, so both
    sides agree. Claims are renewed every 20 min, kept 1 h after publication and expire after 2 h; a
    failing claim write never stops a run.
  - Stress test, 60 writers (30 owners, 30 helpers) on a 300-item pool against a bare remote for 4 min:
    1,948 holds, 0 overlapping, 0 failed writes.
  - Tested against a local bare remote: an owner and three helpers on 16 shared items built each one
    once; a killed helper's 3 claimed items were taken back by the owner after the claim lifetime;
    `merge` over both families had no conflicts.

## Free keys, the 232 chain and the assembly

### Free keys (`--free` mode)

`lean435/tools/freeplan435.py` turns a plan's free keys into a job list for `prod435.py`. For the 232
plan (1b) the list holds 4,215 plain certificates and 210 share certificates, about 4.78 G hints:

| certificates | what they are |
|---:|---|
| 2,570 | 233 seeds, with their widened bounds |
| 1,383 | keys of the 235–237 replays |
| 262 | H8 cuts |
| 210 | free233 share keys, each with its 233 cap |

The 7,289 keys derived by L1 or L2 get no certificate of their own; the 2,832 reuse233 keys that are L1 or L2 of a 233 seed are glue too. They are glued with
`Families.refuted_key_of_wide` or `Families.refuted_key_sub`, as `cert233.proof_term` does. The table of
which seed each key comes from is `lean435/data/freederive_*.json.gz`.

### The 232 chain in 4.35

`lean435/tools/chain435.sh PLAN TAG BOUND` runs the generators read-only, then `port.py`, then
`build.py`. For plan `certplan231_m232_541_1b` with tag `M232B541`:

- 427 modules, 3,483 CPU-s in all.
- The 204 shards took 1,628 CPU-s, 5.1–10.0 s each; in 4.19 they took 3,097 s.
- The ctx cover is split into 12 parts of about 46 s each, each at most 0.54 GB.
- No new fixes were needed.
- `upper_232_of_refuted6SCM232B541 : AllRefuted6S… → AllRefutedShare6S… → AllRefutedCtx6SC… → Floors233 → m ≤ 232`
  prints `[propext, Classical.choice, Quot.sound]`.

### Assembly

`glue435.py` writes one glue module per chunk of the chain's key lists. Each one privately imports the
certificate modules of its keys and publicly states that chunk:

| glue module | statement |
|---|---|
| `Glue6SC<T>D<c>` | `AllRefutedList dirChunk…` |
| `…H8` | the H8 cuts |
| `…S<i>` | the share chunk |
| `…C7_<i>`, `…C8_<i>` | the ctx chunks |

For 232 that makes 218 modules. They need 12,507 certificate modules: 8,082 paid, 4,215 free plain and
210 free share. The top module `Glue6SC<T>` combines the chunks through the lemmas in
`lean435/glue/Glue435.lean` (`allRefutedList_flatten`, `allRefutedShareList_flatten`, `allP_flatten`).

`assemble435.py` compiles every glue module from the certificate interfaces alone. It uses
`audit.py final --out-olean`: a `--setup` file that lists only the public `.olean` of each
certificate, with `strace` running. It then compiles the top module. Last, it audits
`upper_232_435 := upper_232_of_refuted6SC… allRefuted… allRefutedShare… allRefutedCtx…
Floors233Port.floors233` against the axiom whitelist.

**Tested on 4 chunks.** Chunks D57, D61, S24 and C7_50 need 36 certificates, which were produced locally
by `prod435.py run --no-sync` and gathered by `prod435.py collect`. D61 includes L2 terms. All four
glue modules built and all printed `[propext, Classical.choice, Quot.sound]`. Only public `.olean`
files of the certificates were opened. The full top module and the final theorem wait for all the
certificates.

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

## Final audit of the bound 232: `Snake9.upper_232_435` (17 November 2026)

**Verdict: AUDIT PASSED.**

```
public theorem upper_232_435 : ∀ {m : Nat}, Snake m → m ≤ 232
'Snake9.upper_232_435' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Snake m` is the structure of `work/final_lean/Snake9.lean`, ported unchanged in substance by `port.py`. It holds
`vertex : Fin (m + 1) → Fin 512`, injective, with `Adj (vertex i) (vertex j) ↔ i + 1 = j` for `i < j`, where `Adj`
flips one of 9 coordinates. So `m` is the number of edges of an induced path in the 9-cube.

The record is in [`audit232/`](audit232):

| file | contents |
|---|---|
| `final-audit.txt` | the output of `audit.py final` for the final module |
| `UpperBound232_435.lean` | the final module, as generated by `assemble435.py` |
| `assemble-final.log` | the passing full assembly: 218 chunks up to date, top module, final audit |
| `assemble-first-run-FAILED.log` | the first full assembly, which failed (below) |
| `await.log` | the poller's log, 04:19–15:51 UTC |
| `manifest232.jsonl.gz` | the 12,507 manifest lines of the certificates the 232 glue needs (gzip of 25.0 MB `manifest232.jsonl`, sha256 `623d0256…d4335b`; gzip sha256 `c2513ce5…76e90d`) |
| `glue-olean.sha256` | sha256 of the 220 glue `.olean` files built here (218 chunks, `Glue435`, the top module) |
| `spec-olean.sha256` | sha256 of `Snake9`, `AggregateDirection6SCM232B541` and `Floors233Port` as rebuilt here |

The full merged manifest of all four families at the time (27,367 lines, 55.5 MB, both plans) had sha256
`08247ad8715feb4e7802793589853f3e96d5ea364f7ac8e9fcd6c7c7a1eccd23`. It is not committed.

### What was rebuilt locally, and with which commands

On a fresh 4-core, 15 GB machine of environment `snake-in-the-box-9-lean435` (Lean 4.35.0 at `/opt/lean-4.35.0-linux`):

1. **Core:** `prod435.py setup`. 86 modules, 180 s, into `~/l435/prod/core`.
2. **Mathlib v4.35.0:** `cp -r /opt/mathlib4-v4.35.0 ~/l435/mathlib4; lake env true; lake build
   Mathlib.Algebra.BigOperators.Fin Mathlib.Data.Fintype.EquivFin Mathlib.Order.Interval.Finset.Fin Mathlib.Tactic`.
   3,142 jobs, no errors.
3. **Floors:**
   - `floors/tools/fetch.py`: every git blob sha was verified. `FETCH-MANIFEST.tsv` is identical to the committed one.
   - `floors/tools/port_floors.py`: `FLOORS-PORT-MANIFEST.tsv` is identical.
   - `floors/tools/buildk.py --keep-going --jobs 2 --rss-gb 4.5 --big-rx '.*\.Check[0-9]+=9' Floors233Port`:
     1,070/1,070 built, 0 failures.
4. **The 232 chain:** `chain435.sh certplan231_m232_541_1b.json.gz M232B541 232`.
   - The build exited 0, and every `#print axioms` of the chain is within the whitelist.
   - The regenerated `shards6sc_M232B541.sha256` is identical to the committed one, and `auto6sc_M232B541.json`
     differs only in its `seconds` field.
   - The script generated 218 glue chunks plus the top module.
5. **Interfaces:** `prod435.py merge` of `xfer/c435`, `c435help`, `c435free` and `c435freehelp`. Every `.olean`
   was checked against its manifest line's sha256. There were no conflicts.
   - The last certificate, `LocalWindowCert.T012301A24643K27` (51.6 M hints), was published on
     `xfer/c435help/w105` at about 15:36 UTC.
6. **Assembly:** `await435.py --tag M232B541 --chain ~/l435/chain232 --bound 232 --work ~/l435/asm232`.
   - It merged the interfaces again every 15 minutes.
   - It built 217 chunks at 04:22 and the last chunk (`S11`) at 15:47.
   - It then ran `assemble435.py` in full: the top module `Glue6SCM232B541`, then `audit.py final` on the final module.

### What the final audit checked (`audit.py final`)

- **Hashes.** The sha256 of each of the 12,507 certificate interfaces matches the manifest. The 1,692 spec
  modules (chain, core, floors) come from the local rebuild.
- **Clean directory and `--setup`.** The final compile ran with `LEAN_PATH=/nonexistent`. Its setup lists
  17,532 import artifacts: the public `.olean` of 17,320 modules (1.14 GB), plus the IR of the locally built
  spec layer, mathlib and the toolchain.
- **strace.** The final compile opened no file outside the clean directory and the toolchain. Outside the
  toolchain, it opened no non-`.olean` part other than spec-layer IR. It opened no certificate interface at
  all: certificates are private imports of the glue chunks.
  - Each glue chunk was compiled the same way from the public certificate `.olean` files, with the same
    hash checks and the same strace check: no `.olean.private` or `.olean.server` of a certificate was opened.
- **Whitelist.** `#print axioms Snake9.upper_232_435` must be a subset of `{propext, Classical.choice,
  Quot.sound}`.
  - A `sorry` anywhere below would show up as `sorryAx`.
  - A `native_decide` would show up as a `._native.native_decide.ax_*` axiom.
  - So would any declared `axiom`. Step 4 of the Status table at the top showed each of these three cases being caught.

### First run failed, and the fix

The first full assembly (15:47 UTC) printed `AUDIT FAILED`.

```
UpperBound232_435.lean:11:44: error(lean.unknownIdentifier): Unknown identifier `Snake`
Note: A public declaration `Snake` exists but is imported privately; consider adding `public import Snake9`.
'Snake9.upper_232_435' depends on axioms: [sorryAx]
```

- **Cause.** `assemble435.py` generated the final module with private imports only. The public statement
  mentions `Snake`, so it did not elaborate, and Lean used `sorryAx` for the error.
- **Fix.** Commit `01b3c233` adds `public import Snake9` to the final module. The chain, glue and floors stay
  private imports.
- **Rerun.** The rerun reused the 218 chunks and the top module, already built, and passed.
- **Takeaway.** The whitelist check did its job: it rejected the broken final module.

### Caveats

- **Server and private parts are not byte-deterministic.** `audit_floors.sh` stops at its check 3 on this
  rebuild. The `.olean.server` and `.olean.private` of `DirectionWindowBridge7`, `LocalWindowTagsShare` and
  `WindowAutomatonLemmas` differ from `OLEAN-MANIFEST.tsv`.
  - The same parts differ between this machine's own core, chain and floors builds of the same source.
  - All 1,070 sources and all 1,070 public `.olean` files match the manifest. The 30 modules that the core,
    chain and floors trees share have identical public `.olean` files.
  - The audit reads only public `.olean` files of the shared and certificate layers.
  - Check 4, run by hand, gave the same result as recorded: `audit_floors` depends on the three whitelisted
    axioms and opens 24 interfaces.
- **No second kernel.** No `leanchecker` or other second-kernel run was made on the assembled theorem.
- **Kernel checks happened on the farm.** Certificates were kernel-checked where they were built: on the farm
  machines, when their modules were compiled. The auditor trusts that compile through the public `.olean` and
  its stored axiom list, as designed in the Audit section above.

## Final audit of the bound 231: `Snake9.upper_231_435` (17 November 2026)

**Verdict: AUDIT PASSED** (21:45 UTC).

```
public theorem upper_231_435 : ∀ {m : Nat}, Snake m → m ≤ 231
'Snake9.upper_231_435' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Snake` is the same structure as in the 232 section above (an induced path with `m` edges in the 9-cube); the
`Snake9.olean` used here is the same file (same sha256) as in the 232 audit.

The record is in [`audit231/`](audit231):

| file | contents |
|---|---|
| `final-audit.txt` | the output of `audit.py final` for the final module |
| `UpperBound231_435.lean` | the final module, as generated by `assemble435.py` |
| `assemble-final.log` | the full assembly: 372 chunks up to date, `S12` built, top module, final audit |
| `await.log` | the poller's log, 04:49–21:45 UTC |
| `manifest231.jsonl.gz` | the 24,797 manifest lines of the certificates the 231 glue needs (gzip of 50.3 MB `manifest231.jsonl`, sha256 `d1b101fc85840f93f80b678311a17cc4763c613126e4dae027d80c74d485c0e4`; gzip sha256 `ea21bc2d543f4b8b273cd11f5e9ceaa3e1d1d4418122658bcebeb92e783e7398`) |
| `glue-olean.sha256` | sha256 of the 375 glue `.olean` files built here (373 chunks, `Glue435`, the top module `Glue6SC563B1`) |
| `spec-olean.sha256` | sha256 of `Snake9`, `AggregateDirection6SC563B1` and `Floors233Port` as rebuilt here (`Snake9` and `Floors233Port` identical to the 232 audit) |

The full merged manifest of all four families at the time (27,402 lines, 55.6 MB, both plans) had sha256
`ac2ea1cba097db0096edc74f4a328b9b5f3fa0b33ab42fca9b3b22b36d252b2f`. It is not committed.

### What was rebuilt locally, and with which commands

Same machine, core, mathlib and floors as the 232 audit (steps 1–3 there). Then:

1. **The 231 chain:** `chain435.sh milestones/28-combined-identities/data/certplan231_563_1_cap.json.gz 563B1 231
   ~/l435/chain231`.
   - The build exited 0, and every `#print axioms` of the chain is within the whitelist
     (`coverH8_6S563B1` prints `[propext, Quot.sound]`, a subset).
   - The regenerated `shards6sc_563B1.sha256` is identical to the committed one, and `auto6sc_563B1.json`
     differs only in its `seconds` field (not committed).
   - The script generated 373 glue chunks plus the top module; they need 24,797 certificate modules.
2. **Interfaces:** `prod435.py merge` of `xfer/c435`, `c435help`, `c435free` and `c435freehelp` (113 branches at
   the end). Every `.olean` was checked against its manifest line's sha256. There were no conflicts.
   - The last certificate, `LocalWindowCert.T012301A26346K35` (78.8 M hints, split), was published on
     `xfer/c435help/w150` at about 21:38 UTC.
3. **Assembly:** `await435.py --tag 563B1 --chain ~/l435/chain231 --bound 231 --work ~/l435/asm231 --jobs 2`,
   polling every 20 minutes (every 2 minutes from 21:37, after a restart by PID; built chunks were kept).
   - It built 233 chunks at 04:55 and the rest as their certificates arrived; the last chunk (`S12`) at 21:41.
   - It then ran `assemble435.py` in full: the top module `Glue6SC563B1` (9.9 s), then `audit.py final` on the
     final module (compile 190 s, audit 207 s).

### What the final audit checked (`audit.py final`)

The same checks as for 232:

- **Hashes.** The sha256 of each of the 24,797 certificate interfaces matches the manifest. The 1,858 spec
  modules (chain, core, floors) come from the local rebuild.
- **Clean directory and `--setup`.** `LEAN_PATH=/nonexistent`; 29,988 import artifacts, the public `.olean` of
  29,776 modules outside the toolchain (1.36 GB).
- **strace.** No file outside the clean directory and the toolchain; no non-`.olean` part outside the toolchain
  other than spec-layer IR; no certificate interface opened by the final compile (they are private imports of
  the glue chunks). Each of the 373 glue chunks was compiled the same way from public certificate `.olean`
  files, with hash and strace checks, and printed AUDIT PASSED.
- **Whitelist.** `#print axioms Snake9.upper_231_435` ⊆ `{propext, Classical.choice, Quot.sound}`; no `sorryAx`,
  no `native_decide` axiom, no declared axiom.

### Split certificates

Five certificates of this plan were built by the split route of [SPLIT.md](SPLIT.md): `T012301A36264K45`,
`T012301A46246K33`, `T012301A33436K47`, `T012301A35353K20` and `T012301A26346K35` (44–93 M core LRAT hints,
8 or 16 kernel part modules each). Each is a module `LocalWindowCert.N` with the same public `refuted` statement
as a stock certificate; its kernel checks are in part modules `LocalWindowCertSplit.N.*`, which it imports
privately and which were built on several machines. How they were checked:

- **On the farm** (SPLIT.md): every part's base modules (Cnf, D*, Ps) had the same `.olean` sha256 as the
  final machine's; the final module compiled against all parts; an interface-only audit of each published
  `.olean` printed `[propext, Classical.choice, Quot.sound]`.
- **Here:** the public `.olean` of each matches its manifest line (sha256 `2b46265a…`, `af4922f3…`,
  `249d7c18…`, `2fc0915b…`, `8b24f3e1…`), checked in every compile that uses it. Their glue chunks (`S12`,
  `S13`, `S14`) compiled from interfaces with strace clean. A separate interface-only test at 19:55 UTC that
  imported `T012301A36264K45` and `T012301A46246K33` passed with 17 import artifacts: no part module and no
  `.olean.private`/`.olean.server` was needed or opened.
- The axiom list stored with a split certificate's `refuted` was computed when its final module was compiled
  against all its parts, so a `sorry` or `native_decide` in a part would show in that list and hence in the
  final whitelist check (the same trust model as for stock certificates).

### Caveats

- The caveats of the 232 audit apply unchanged: non-deterministic `.olean.server`/`.olean.private` of three
  floors modules (public `.olean` all match), no second-kernel (`leanchecker`) run, and kernel checks done on the
  farm and trusted through the public `.olean`.
- For the five split certificates, the kernel checks of their parts ran on several farm machines; this audit
  sees only the final public `.olean`.

### Lessons for future plans (details in SPLIT.md)

- Plan hint estimates of unmeasured share items were off by up to 124x (real core proof against plan estimate;
  the cores step's full-proof estimate was up to 219x the plan). Run the cores step of every item early and
  schedule on its estimate (x ~0.55 for the core proof), not on the plan's.
- Above ~5 M estimated hints, the stock replay search (21 CaDiCaL runs x up to 5 shrinking rounds, one at a time
  under the memory gate) is the wrong default: use `bigreplay435.py` (3 configurations in parallel, one round).
- The stock generator `gen_lean_lrat_v3.py` runs out of memory near 90 M hints on 15 GB machines; use
  `genv3stream.py` (same output bytes, < 0.4 GB).
- Above ~20 M core-proof hints, build a split certificate (`splitfarm435.py prepare / part / final`, 8-16 parts of
  3-6 M hints, 2-6 GB each) instead of one module of 6-10+ h.

## Second-kernel checks of the assembly (17–18 November 2026)

The caveat "no second kernel" above is now narrowed. Some parts were re-checked by a second pass of Lean's
C++ kernel, and the assembly (glue, top module, final module) by an **independent** kernel, nanoda
(Rust). The certificates' own proofs were **not** re-checked: their kernel checks stay single runs on the
farm. Re-checking them means rebuilding them from source (about 2,600 Lean CPU-hours for 231), or
sampling. The tools are in `lean435/tools`. The 4.35 toolchain here ships `leanchecker`, `nanoda_bin`
0.4.19, `leanexport` and `lean4lean`.

| what | kernel | 231 | 232 | record |
|---|---|---|---|---|
| final module recompiled with `-o` (`audit.py final --out-olean`) | C++ (compile) | AUDIT PASSED again | AUDIT PASSED again | `audit*/final-audit-rerun-out-olean.txt` |
| glue chunks, `Glue435`, top module, final module: kernel replay at interface level (`ifacecheck.lean`) | C++, second pass | 376 modules, 14,746 constants, 0 failures, 340 s | 221 modules, 12,394 constants, 0 failures, 226 s | `audit*/ifacecheck.log` |
| the same modules, exported (`exportiface.lean`) and checked from the export (`xkernel435.sh`) | **nanoda** (independent) and `leanchecker --from-export` (C++) | 376 modules, 208,119 declarations, both kernels accept all | 221 modules, 124,819 declarations, both accept all | `audit*/xkernel.log`, `audit*/assumptions.txt.gz` |
| spec layer: core, chain, floors (1,553 modules), stock `leanchecker`, one module per process | C++, second pass | in progress | (same core and floors; 232 chain not run) | see below |

**Why a custom script.** Stock `leanchecker` loads the `.olean.server` and `.olean.private` of every import.
The certificates publish only their public `.olean`, so on a glue module it stops at the first certificate
import. `ifacecheck.lean` is leanchecker's `replayFromImports` with the imports loaded at the exported level.
Each certificate gets its public `.olean` as its only artifact.

**What the independent check assumes.** `exportiface.lean` exports the closure of a module's own constants.
Imported constants whose bodies are not exported become axioms of the export, and nanoda's
`permitted_axioms` names every one of them, so nothing else can be assumed. Over all 231 modules these
assumptions are:
- the 24,797 certificate theorems `…refuted` (exactly the plan's certificates, pinned by the manifest);
- 389 theorems and definitions of the spec layer and, in the top and final modules, the glue chunk theorems
  that those modules combine (each chunk is checked separately);
- 30 toolchain constants without exported bodies, such as `Eq.symm`, `Nat.mod_lt`, `Nat.xor` and `Nat.repr`.

For 232 the counts are 12,507, 234 and 30. So the independent kernel checks the assembly *given* the
certificate statements and the spec-layer theorems. The spec layer has only the C++ second pass. The final
module's export assumes `upper_231_of_refuted6SC563B1` (the chain) and `Floors233Port.floors233`, and checks
that the theorem follows.

**Negative test.** In the export of chunk S14 of 231, the statement of the chunk's theorem was replaced by
another proposition. nanoda failed (exit 101) and `leanchecker --from-export` rejected the export.

**lean4lean.** The `lean4lean` binary in this toolchain was built for a 4.35 nightly
(`4.35.0-nightly-2026-09-06`). It refuses every 4.35.0 `.olean` ("incompatible header"), and it has no
export mode. It was not used.
