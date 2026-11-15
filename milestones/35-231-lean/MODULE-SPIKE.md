# Module-system spike: kernel-check certificates where they are built, audit from interface files

Spike of 15 November 2026 (branch `research/unconditional-241`). It replaces the source-reading
claims of `AUDIT-SCALING.md` option (b) with experiments. Toolchain: **Lean 4.35.0** (commit
`eb6cafb7`), the newest stable release on 15 November 2026. v4.36.0 exists only as `-rc2`. It is
the release that mathlib's `v4.35.0` tag pins, and it has every feature in question: private
imports are not loaded (from 4.25), and axiom lists are stored per export (from 4.30).

- **Download.** From `github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst`
  (594 MB, sha256 `7289597a…268f6d`), unpacked with Python `zstandard` into `/dev/shm/leanspike`.
  Static libraries, LLVM and the `Lean.*` private and `.ir` parts were skipped, leaving 1.2 GB.
- **Untouched.** The existing 4.19.0 toolchain, every lake file, every `.olean` and every audited
  module were left alone. All builds were direct `lean -o` calls, one at a time, at `nice -n 10`,
  under a 1.9 GB `RssAnon` watchdog.
- **Cleanup.** `/dev/shm/leanspike` was deleted at the end. It was also deleted once by the
  coordinator during the 08:15 pause, then re-downloaded.
- **Incident.** One early toy (a 1 MB literal list decoded with `List.++`) reached 8 GB and was
  OOM-killed at 08:08. The toys were shrunk after that.
- **Blocked hosts.** `releases.lean-lang.org` and `lean-lang.org` are blocked by the proxy (403).
  `github.com` release downloads and `raw.githubusercontent.com` work.

## Answer: GO, with conditions

**Yes. In Lean 4.35, a certificate can be kernel-checked on the machine that builds it, and the
final audit can run on a small machine that holds only the public interface `.olean` of each
module.** Measured on the toy chain and on a real certificate from this repository
(ctx-8 `C801234032A544643K15`, 204,129 hints):

- The final module imported **only public `.olean` files**: 19 files and 4.8 MB for the real
  certificate plus its support stack. The certificate's own interface is **8.6 KB**, against
  0.86 MB for the 4.19 Cnf + replay pair.
  - It never opened the certificate's `.olean.private` (589 KB), its Cnf module, or the
    certificate's private imports (`LratV3`, `ProofPack`, `LocalWindowCnfPack`).
  - It finished in **0.6 s with 58 MB of anonymous memory**. `#print axioms` printed
    `[propext, Classical.choice, Quot.sound]`.
- **`sorry`, `native_decide` and `axiom` in a certificate two levels down are all reported** by
  `#print axioms` in a final process that has only the chunk's 3.6 KB `.olean`. The information
  comes from axiom lists stored in that `.olean` (`exportedAxiomsExt`), not from proof bodies.
- **The trust model is the same as today's in kind.**
  - The final kernel checks the final module against the *statements* of the imported theorems.
  - Each certificate's proof was checked by the kernel of the machine that compiled it.
  - The axiom list was computed by that machine's elaborator when it wrote the `.olean`.
  - Today's audit also trusts previously built `.olean` files: 4.19 never re-checks imports, and
    233 took 19 cloud-built certificates on trust.
  - **What is lost:** the audit machine can no longer re-walk or re-check the proof bodies,
    because it does not have them.
  - **What must be added:** a **hash manifest**. A stale or swapped *specification* `.olean` lets
    the final module prove `False` with clean axioms. This was shown in both 4.35 and 4.19, so it
    is not new, but interface-only audits remove the bodies that a full re-check could have used
    to catch it.

**Smallest audit procedure that still detects `sorry`, `native_decide` and extra axioms:**

1. **On each worker**, build the certificate module and its chunk module with Lean 4.35.
   - Record the sha256 of every output part (`.olean`, `.olean.server`, `.olean.private`, `.ir`,
     `.ir.sig`) and of the source.
   - Push only the public `.olean` (about 9 KB per certificate, or one chunk `.olean` of a few KB)
     plus a manifest line to git.
   - Optional extra step: run `leanchecker <Module>` there. It re-checks the module's constants
     from the full `.olean` in a fresh kernel environment. It ships with 4.35, together with
     `lean4lean` and `nanoda_bin`.
2. **On the audit machine:**
   - Rebuild the small *specification and support* layer from git source. That is everything a
     public statement mentions: the core logic, the chain and mathlib.
   - Check that the hashes of its public `.olean` equal the hashes in the worker manifests. 4.35
     output is byte-deterministic (measured).
   - Check the sha256 of every interface `.olean` against the manifest.
3. **Compile the final module** with a `--setup` file whose `importArts` lists exactly those
   interface files, as lake does.
   - Require `#print axioms` of the final theorem to be a subset of
     `[propext, Classical.choice, Quot.sound]`.
   - That is a whitelist. Grepping for `sorryAx` or `Lean.ofReduceBool` is not enough: in 4.35,
     `native_decide` shows up as an auxiliary axiom named `…_native.native_decide.ax_1_1`.
4. **Spot-check workers independently**: rebuild a random sample of certificates from source on
   another machine and compare the hashes of their public `.olean`.

**Cost:** a port of the whole closure to 4.35 `module` syntax (everything a `module` imports must
itself be a `module`, measured), a matching mathlib, and a rebuild of every certificate that the
231 theorem imports. The kernel measured **0.68x the 4.19 time** on the real replay, so the rebuild
is cheaper than the original build. Porting the 17-file support stack of the real certificate took
**4 one-line proof fixes plus a mechanical header conversion**. Estimates are in the migration
section.

## Experiments

### Toy chain (module syntax, core Lean only)

- **`Toy.Spec`.** `@[expose] public section` with small definitions:
  - `hw n acc k`, which folds the 128 16-bit words of a literal into a hash;
  - `check : List Nat → Nat → Nat`;
  - `Spec t := ∃ l : List Nat, check l 0 = t`.
- **`Toy.C1`-`C3`.**
  - `noncomputable def raw : List Nat := [0x…, …]`, private: 1,024 hex literals of 256 bytes,
    2.1 MB of source;
  - `theorem raw_ok : Toy.check raw 0 = h := by decide +kernel`, private;
  - `public theorem c_ok : Toy.Spec h := ⟨raw, raw_ok⟩`.
- **`Toy.A`.** `public import Toy.Spec`, then **non-public** `import Toy.C1/C2/C3`, then
  `public theorem A_ok : Spec h1 ∧ Spec h2 ∧ Spec h3`.
- **`Toy.F`.** `public import Toy.Spec`, `import Toy.A`, `public theorem final : Spec h2 := A_ok.2.1`,
  `#print axioms`.
- **Bad variants.**
  - `CSorry`: `raw_ok := sorry`.
  - `CNative`: `raw_ok := by native_decide`. It needed a computable `raw` and
    `public meta import Toy.Spec`.
  - `CAxiom`: `axiom cheat : False` and `raw_ok := cheat.elim`.
  - `ABad` imports C1 and the three bad modules. `FBad` imports `ABad`.

Build cost per C module (256 KB of payload): 9.4-9.9 s and 1.21 GB `RssAnon`. Most of the memory
goes to elaborating the literal list. A 512 KB payload needed 2.36 GB, so it was not used. A and F
each built in 0.2 s, at 44-55 MB.

### (a) Output files and what an importer opens

**A module build writes, per module:**

- `.olean`: the exported, public part;
- `.olean.server`: language-server data such as docstrings and ranges;
- `.olean.private`: the private part, holding non-exposed bodies, proofs and private declarations;
- `.ir`, `.ir.sig`: the compiler IR and its signature;
- `.ilean`: with `-i`. Lake also writes a `.c` file and a `.hash` per part.

A non-`module` file writes a single `.olean`, as in 4.19, with no private split.

| module | `.olean` | `.olean.private` | `.olean.server` | `.ir` |
|---|---:|---:|---:|---:|
| toy `C1` (256 KB payload) | 3,528 | 518,888 | 1,408 | 1,360 |
| toy `A` | 3,664 | 1,344 | 864 | 1,672 |
| toy `Spec` | 39,416 | 12,480 | 2,512 | 8,424 |
| real `LocalWindowCtxUnsat.C801234032A544643K15` (module port) | **8,616** | 588,896 | 6,136 | 1,728 |
| real `LocalWindowCtxCnf.C801234032A544643K15` (module port) | 4,832 | 206,936 | 12,464 | 1,792 |
| same two, 4.19 (non-module) | 613,392 + 250,184 | — | — | — |

A `def` that is not `noncomputable` is compiled. With a computable `raw`, toy C1 produced a
199 KB `.ir` and a 482 KB `.c`. Certificate data must stay `noncomputable`, as the generators
already make it.

**Files opened** (`strace -e openat`):

- **Plain `lean` (no `--setup`)** loads `.olean`, `.olean.server` and `.olean.private` for every
  module it loads ("opportunistically load all available parts", `readModuleDataPartsOfMod`). It
  **fails** if `.olean.server` or `.olean.private` of a loaded module is missing.
- **Under the module system, what is loaded is decided per import.**
  - `F` → `import A` → `import C*`: compiling F opened **only `A.*` and `Spec.*`, never a
    `C*` file**. That is the `needsData := needsData && (i.isExported || importAll)` rule.
  - The private import of a non-root module is not visited at all.
- **With a lake-style `--setup` JSON** (`importArts` = the files per module), lean reads only the
  listed files.
  - Lake itself listed `Spec.olean` + `Spec.olean.server` + `Spec.ir.sig` + `Spec.ir` for an
    importer, and **never `.olean.private`**.
  - Compiling `A` with `importArts` set to `C*.olean` only (no server, private or IR files)
    worked. It opened exactly `C1.olean`, `C2.olean`, `C3.olean` and `Spec.olean`.

**Which files must exist two levels up:**

| file | needed by `F` (imports `A`, which privately imports `C`) |
|---|---|
| any `C*` file | none |
| `A.olean` | yes, when lean is run with `--setup` |
| `A.olean.server`, `A.olean.private` | only without `--setup` |
| `A.ir`, `A.ir.sig` | not needed for a proof-only module (empty IR list in `--setup` worked) |

### (b) Delete the big files and rebuild F: works

| run | files present | result |
|---|---|---|
| F, plain `lean` | `C*.olean.private` moved away | ok, `'Toy.final' does not depend on any axioms` |
| F, plain `lean` | **every `C*` file** moved away | ok, same output, opened only `A.*`, `Spec.*` |
| F, plain `lean` | also `A.olean.private`/`.server`/`.ir*` away | **error**: `failed to open file 'A.olean.server'` |
| F, `--setup` with only `A.olean`, `Spec.olean` | **only these two files** (3.6 KB + 39 KB), `LEAN_PATH=/nonexistent` | **ok**, axioms clean, only those two files opened |
| A, plain `lean` | `C*.olean.private` away | error: `failed to open … C1.olean.private` |
| A, `--setup` with `C*.olean` + `Spec.olean` only | `C*.olean.private`/`.server`/`.ir` absent | **ok** |

**Real certificate.** The 4.35 module port of the ctx-8 certificate and its support stack is
described in (e). For it, a final module `Final` was compiled with `--setup` listing only the
public `.olean` of 18 support modules and of `LocalWindowCtxUnsat.C801234032A544643K15` (19
files, 4.8 MB in all):

```lean
module
public import LocalWindowShareCtx
import LocalWindowCtxUnsat.C801234032A544643K15
public theorem final_ctx8 : RefutedShareFrom (winOf [0, 1, 2, 3, 4, 0, 3, 2])
    [(1, 21), (5, 5), (4, 4), (4, 4), (6, 21), (4, 4), (3, 3)] 12 15 2 :=
  C801234032A544643K15.refuted
#print axioms Snake9.LocalWindow.final_ctx8
```

- Output: `depends on axioms: [propext, Classical.choice, Quot.sound]`, 0.6 s, 58 MB `RssAnon`.
- Opened: 15 public `.olean` files.
- Not opened: the Cnf module, `LratV3`, `ProofPack`, `LocalWindowCnfPack`, and every
  `.olean.private`.

**So a final audit can run on a machine that never received the certificate data.**

### (c) `#print axioms` across the boundary: all three detected

`FBad` was compiled with `--setup` listing only `ABad.olean` and `Spec.olean`, so no C file of
any kind was present:

```
'Toy.ABad_ok' depends on axioms: [sorryAx,
 _private.toy.Toy.CAxiom.0.Toy.CAxiom.cheat,
 _private.toy.Toy.CNative.0.Toy.CNative.raw_ok._native.native_decide.ax_1_1]
'Toy.finalBad' depends on axioms: [same three]
```

The good chain gives `'Toy.final' does not depend on any axioms`. The real one gives
`[propext, Classical.choice, Quot.sound]`.

- **Where it comes from** (`Lean/Util/CollectAxioms.lean`, 4.35):
  - `exportedAxiomsExt.exportEntriesFnEx` runs when an `.olean` is written. It computes, with the
    private environment, the sorted axiom list of **every exported declaration** of the module,
    and stores it in the `.olean`.
  - `collectAxioms` in an importer uses the stored list for any imported constant and does not
    descend into it: "axiom collection never crosses module boundaries".
  - Lists compose. `A`'s stored list for `A_ok` was computed from `C`'s stored lists, so a bad
    axiom two or more levels down is carried up.
- **Fails safe.** The following is from reading the source, not tested. If an imported constant
  has no stored entry (for example an `.olean` written without the extension), `collect` falls
  back to the constant as the importer sees it. A theorem exported without its body is an
  `axiomInfo` there, so it would itself be **listed as an axiom**, which a whitelist rejects.
- **`native_decide` has changed form in 4.35.** It now introduces an auxiliary axiom
  `…._native.native_decide.ax_<n>`, not a use of `Lean.ofReduceBool`. An audit that greps for
  `ofReduceBool` would miss it. **Whitelist** `{propext, Classical.choice, Quot.sound}` instead.
- **A `sorry` is only a warning** (`declaration uses 'sorry'`). The build succeeds, so the
  per-module build log is not a sufficient check. The final `#print axioms` is.
- **`leanchecker` does not catch these.** Run on the worker, `leanchecker Toy.CSorry` and
  `leanchecker Toy.CAxiom` both pass. It re-checks kernel validity, and `sorryAx` and `cheat` are
  valid axioms. It complements the axiom whitelist but does not replace it.

### (d) Trust model

**What the kernel of the final process checks.**

- Each declaration of the final module, against the environment built from the interface files.
- An imported non-exposed definition is an opaque constant.
- An imported theorem is its statement: under the module system it is exported as an `axiomInfo`
  (`AddDecl.lean`; `Environment.lean` says "a theorem may be weakened to an axiom when exported").
- Definitions the statement mentions must be `@[expose]`d, so their bodies are in the public
  `.olean` and the kernel can unfold them. In the real port, `winOf`, `RefutedShareFrom` and the
  checker functions are exposed.

**What it takes on trust from the `.olean`.**

1. The statement of each imported theorem, and that it was kernel-checked when its module was
   compiled.
2. The stored axiom list of each imported declaration.
3. That the definitions an imported statement refers to *by name* are the ones it was checked
   against.

**Comparison with today (4.19).**

- Point 1 is the same as today. Lean never re-checks imported `.olean` files: an `.olean` with a
  forged constant would be accepted in 4.19 too. 233 also accepted 19 cloud-built certificates,
  and its audit rebuilt only the last module.
- Point 2 is new in form. Today `#print axioms` walks the bodies in the audit process. In 4.35 the
  list was computed by the worker's elaborator, and a forged `.olean` could carry a forged list.
  But a forged 4.19 `.olean` could equally carry a forged body. In both cases the trusted
  computing base is "the Lean binary that wrote the file, run honestly".
- Point 3 is the real hazard, and it is **not** new.
  - **Experiment:** `Spec` was rebuilt as `def Spec (t : Nat) : Prop := False`. The *old*
    `A.olean` was reused, and `public theorem evil_false : False := Toy.A_ok.1` was compiled
    against it.
  - **Result:** accepted, `'evil_false' does not depend on any axioms`.
  - **Same in 4.19:** with non-module files, an old `A.olean` (`a_ok : Spec 1 := rfl` with
    `Spec t := t = t`) was imported against a new `Spec.olean` (`Spec t := False`).
    `theorem evil : False := a_ok` was accepted with no axioms.
  - Neither version records a hash of the imported modules in an `.olean`. Lake's `.trace` files
    hold input hashes (`importArts`, `depHash`), but they are build metadata that lean does not
    check.
  - With the full files, a re-check of every module against its imports would catch such a
    mismatch: `leanchecker` per module replays each body against the imports. With interfaces
    only, the audit machine cannot do this.

**Does an interface file carry a hash of the full module?** No field of the kind was found or
used. The `.olean`, `.olean.server` and `.olean.private` are separate compacted regions, read with
the earlier parts as bases (`CompactedRegion.read … #[main.2, server.2]`). Lake writes a `.hash`
per part. The mitigation is therefore a manifest that we keep ourselves:

- **Byte determinism (measured).** Rebuilding toy `C2` twice from source gave identical sha256
  for `.olean` (`9032a84b…`), `.olean.server` and `.olean.private`.
- So a manifest of `(module, source sha256, sha256 of each part)` can be:
  - **checked on the audit machine for the public parts**, by rebuilding the small spec and
    support layer locally and comparing; this closes hazard 3;
  - **re-verified anywhere for any certificate**, by rebuilding it from source.

**Net.** No weaker than today *for an honest build*: the same kernel checked every proof, only
on a different machine and at a different time. Not as strong as a hypothetical full re-check on
the audit machine, which today is possible in principle (the bodies are there) but which 233 did
not do. The procedure in the Answer (manifest, local rebuild of the spec layer, axiom whitelist,
random independent rebuilds) restores what can be restored.

### (e) Kernel performance on a real replay

The real certificate pair `LocalWindowCtxCnf/Unsat.C801234032A544643K15` (204,129 hints, 10,386
lemmas, 4 segments) is already in `milestones/35-231-lean/lean/`, so nothing was regenerated.

**Import closure:** 20 files.

- 17 support modules of `work/final_lean`, 7,925 lines:
  - `LocalWindowModel`, `LratV3`, `LocalWindowDirModel`, `LocalWindowTags`,
    `LocalWindowCnfPack`, `LocalWindowTagsW`;
  - `LocalWindowShareModel`, `LocalWindowTagsShare`, `LocalWindowTagsSW`,
    `LocalWindowTagsSharePacked`;
  - `Snake9`, `PathStructure`, `LocalWindowBridge`, `LocalWindowDirKeys`, `LocalWindowDirBridge`,
    `LocalWindowShareBridge`, `LocalWindowShareCtx`.
- `ProofPack`.
- The Cnf + replay pair.
- Core only, no mathlib.

**Porting, as non-module files first** (the four proof fixes, plus one cut for memory):

1. `LratV3` l.631: `rw [Option.mem_toList, Option.mem_def, Option.some.injEq] at hy` no longer
   matches, because `Option.mem_toList` now rewrites further. Changed to `simp only […] at hy`.
2. `LocalWindowTags` l.137: `Nat.log2` is now defined by fuel recursion, so `Nat.log2.eq_1` has a
   different shape. Changed to `rw [Nat.log2_def, lg]`.
3. `LocalWindowTags` l.496 and `LocalWindowTagsW` l.428: after `congr 1` the goal is already
   closed ("No goals to be solved"). Wrapped the next line in `try (…)`.
4. `LocalWindowBridge` l.310/564/576: `simpa using h` no longer unfolds `mkPerm` and `cnt`.
   Changed to `simpa [mkPerm] using …` and `simpa [cnt] using h`.
5. `Snake9`: its witness section (the two `by decide` over `Fin 192 × Fin 192`) needs more than
   1.9 GB **in 4.19 as well** (killed at 1.9 GB after 25 s). It was cut from the spike copy
   because nothing in the closure uses it. Not a regression.

Beyond these, the support stack gave 188 deprecation warnings (`if_pos` → `ite_eq_left`,
`List.take_succ`, `Int.ofNat_eq_coe`, …) and 8 unused `simp` arguments, and nothing else.
**The two certificate files compiled unchanged.**

**Module port.**

- **Mechanical script:** `module` header, `import` → `public import`, and the whole body in
  `@[expose] public section … end`. With it, all 17 support modules and `ProofPack` built **with
  no further change**.
- **Certificate modules:**
  - Cnf: `module` header only. Its imports and declarations are private.
  - Replay: `module`, `public import LocalWindowShareCtx` and `import all
    LocalWindowCtxCnf.<N>`, so it sees the Cnf data and bodies. It adds one public theorem whose
    statement uses literal parameters:
    `public theorem refuted : RefutedShareFrom (winOf [0,1,2,3,4,0,3,2]) [(1,21),…] 12 15 2 := TagsSW.refutedShareFrom_of_sat sat unsat`.
- **Pitfall:** private names are mangled with the *module name*, which plain `lean` derives from
  the path relative to `--root`. Without the right `--root`, `import all` cannot resolve the private
  names, and `autoImplicit` then turns them into free variables. The symptom is "Expected type must
  not contain free variables". Lake sets the root correctly.

**Timings.** One process at a time, `nice -n 10`, same machine. The 4.19 runs used the existing
4.19 support `.olean` from `work/final_lean/.lake` (read only), with output to `/dev/shm`.

| module | 4.19.0 wall / kernel | 4.19 peak RssAnon | 4.35.0 wall / kernel | 4.35 peak RssAnon |
|---|---|---|---|---|
| `LocalWindowCtxCnf.C801234032A544643K15` | 28.7 s | 0.96 GB | 14.5 s (module: 15.1 s) | 0.73 GB |
| `LocalWindowCtxUnsat.C801234032A544643K15` | 35.1 s / **33.5 s** type checking | 1.30 GB | 24.1 s / **22.7 s** type checking (module: 25.3 s) | 1.22 GB |
| final audit of this certificate | (imports the full 0.86 MB pair) | — | **0.6 s**, 4.8 MB of interfaces | 0.06 GB |

- **Kernel ratio 4.35/4.19: 0.68** on the replay. This is one certificate, not a benchmark. One
  plausible reason is the changed `Nat`/`List` reduction in core, but that was not analysed.
- The `module` form costs nothing measurable over the non-module form.
- Memory is about the same.

## Migration estimate

**The rule.** Measured: `cannot import non-\`module\` Old from \`module\``. Every file in the import
closure of a `module` must itself be a `module`. Non-module files may import modules. So the
final file, the chain, the floors and every certificate must all be `module`s in 4.35.

**Closure of `UpperBound233`** from source (`import` graph over `work/spectral/stronger`,
`work/final_lean` and `work/spectral/.verification/chain`), with the file counts of
AUDIT-SCALING.md for what has no source in the repository:

| layer | files | lines | must move to 4.35 | must be `module` | expected breakage |
|---|---:|---:|---|---|---|
| core certificate logic in `work/final_lean`: checker v3, tags and share stack, bridges, `Snake9` (17 measured) and other checker variants (`LratFast*`, `LratCheckO*`, `LocalWindowDir*`, `LocalWindowSat*`, `LocalWindowFamilies`, …) | 67 | 46,506 | yes | yes, `@[expose] public section` | measured on 17 files / 7.9k lines: 4 one-line fixes and a mechanical header. Extrapolated: 1-2 days for the rest |
| data-carrying modules in `work/final_lean` that are not `LocalWindowCnf`/`Unsat` (key tables, glue, dir/share replay data) | 1,581 | 118,383 (105 MB) | yes | yes; data private, statements public | generator change only |
| generated certificate sources in the repository (`LocalWindowCnf`, `LocalWindowUnsat`, `LocalWindowCtx*`) | 6,065 | 2,983,976 (453 MB) | yes (rebuild) | yes: Cnf private, replay `import all` Cnf plus one public `refuted` | none seen in the 2 files tried. Generators must emit the new header and the public statement with literal parameters |
| replay modules imported as `.olean` only, with no source in the repository | ~18,400 (22,963 replay + 4,515 Cnf in AUDIT-SCALING, with the above) | — | yes | yes | **sources must be regenerated** from the cores and LRAT proofs (or by re-running the solver) |
| spectral chain `work/spectral/stronger` (+2 in `.verification/chain`) | 175 | 23,119 | yes | yes | unknown. 5 files import mathlib (`AggregateSingletonBound`, `CubeCoordinateAlgebra`, `EndpointGroups`, `FreshCoordinates`, `SquareIncidence`): `Mathlib.Tactic` ×3, `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Fintype.EquivFin`. Mathlib renames between 4.19 (spring 2025) and 4.35 are the main risk: likely days, not measured |
| floors port from main (FLOORS.md) | 1,044 | not counted (sources outside the repository, regenerable from `data/main_floor_modules.json`) | yes | yes | same kind as the core. 2.3 CPU-hours to build in 4.19, including 23 LRAT checks of up to 6.24 GB |
| mathlib | ~2,781 files in the 233 closure, with dependencies (1.89 GB in 4.19) | — | tag `v4.35.0` pins `leanprover/lean4:v4.35.0` and is in `module` syntax (checked: `Mathlib/Algebra/Group/Defs.lean` starts with `module`) | already | download of the `Mathlib.Tactic` closure: its cache host was not tested here |

**Kernel-hours.**

- Every certificate the new final theorem imports must be rebuilt, because `.olean` files are tied
  to the toolchain.
- For the 233 set, the measured ratio of 0.68 gives **about 145 kernel-hours instead of 210**.
  There is one data point, so read it as 110-210. Add the floors (about 1.6 CPU-hours scaled),
  the logic layer (minutes) and mathlib (hours from source, or a download).
- **If the 231 final theorem does not need the 233 certificates** (if 231 is proved from its own
  certificates), only the 231 certificates are built at all, and those must be built anyway.
  Building them directly in 4.35 costs nothing extra and is faster per hint.

**Work estimate.**

| item | estimate |
|---|---|
| logic layer + floors + chain port to 4.35 modules | 3-6 days, mostly mathlib drift in the 5 chain files and floors volume (not measured) |
| generator changes (header, private data, public `refuted` statement, chunk modules with private imports) | 1 day |
| audit driver: manifest, `--setup` writer, hash checks, axiom whitelist | 1 day |
| rebuild of the certificates the final theorem needs | 0.68 × 4.19 kernel time |

**Order.**

1. Port the 17 support modules and the ctx toy.
2. Re-run `build_toy.sh`'s axiom audit in 4.35.
3. Generate 231 certificates directly as 4.35 modules.
4. Port the chain, the floors and mathlib last.

## Alternatives (one paragraph each)

**Import without the data in 4.19.** Not available (AUDIT-SCALING §3c-d, re-confirmed by reading:
4.19 `importModulesCore` always loads the transitive closure). The only ways to cut the closure
are:

- state each certificate as an `axiom` in a small file, plus an out-of-band check that a worker
  proved the same statement, which **changes the trust model** (the final theorem depends on
  named axioms);
- or **`.olean` surgery**: rewrite a 4.19 `.olean` so that theorem values are dropped or turned
  into `axiomInfo`, and drop its imports. That is exactly what the 4.25+ exporter does, but done by
  our own tool outside Lean. Its output would make `#print axioms` either list the stripped
  theorems as axioms or, if forged, hide them. It needs trust in a non-kernel tool written by us.
  **Not recommended.**

**Self-contained lemmas per cloud machine, union checked by a small module.** This is what the
module interface gives, soundly, in 4.35. Each worker proves `chunk_k : AllRefuted… chunk_k`, a
small statement over exposed small definitions, and exports only that. The final module imports
the chunk interfaces. The `.olean` of a chunk that privately imports 100 certificates is a few KB
(toy `A`: 3.6 KB for 3), so 231's 20,000 certificates in 200 chunks give a final closure of about
200 small files plus the spec layer. That is well below `vm.max_map_count`, and the
disk-and-transport wall disappears: about 9 KB per certificate goes through git. In 4.19 the same
split exists only for elaboration (`allRefuted_of_merge`). The final process still loads
everything.

**Extra assurance on the worker.** 4.35 ships `leanchecker`, which replays a module's constants
from its full `.olean` into a fresh kernel. It took 7.9 s and 1.58 GB on toy `C1`, about the cost
of the original check. 4.35 also ships `lean4lean` and `nanoda_bin`, independent kernels that read
the `leanexport` format. A worker could run one of them on each certificate before publishing its
interface. That narrows "trust the worker's Lean run" to "trust that the worker ran these and
reported honestly". It was not measured beyond `leanchecker` on the toy.

## What could not be verified here

- **Lake end to end.** `lake build` was used once on the toy; that is where its `--setup`
  `importArts` came from. Lake 5 has no visible `-j`, and `LAKE_JOBS` did not stop parallel `lean`
  processes, so all later builds used direct `lean` calls. Not checked:
  - how lake behaves on an audit machine that has interface `.olean` files but no sources and no
    `.olean.private`;
  - lake's artifact cache.
  The audit driver should write the `--setup` JSON itself, as done here.
- **One real certificate.** Only one real certificate was timed (0.68x). Not tested in 4.35:
  stack depth, the 7.4 GB largest 233 replay, and the checker variants `LratFast*` and `O5k`.
- **The other layers.** The chain, the floors, mathlib drift and the rest of the logic layer were
  not ported; their estimates are extrapolations. The mathlib cache host was not probed.
- **Scale.** No final audit was run with thousands of interface files. RAM and time are expected
  to be tiny (58 MB and 0.6 s for 19 files), but this is not measured at scale.
- **Fail-safe without stored lists.** That an `.olean` lacking `exportedAxiomsExt` entries makes
  the audit list theorems as axioms is from reading `CollectAxioms.lean`, not tested.
- **Determinism.** Byte determinism was measured on one toy module (two rebuilds), not on real
  certificates or across machines.
- **4.19 baselines.** The 4.19 run of the certificate pair used the existing 4.19 support
  `.olean`, not a fresh build. The 4.35 run used the spike port (Snake9's witness section cut).
