# Lean framework for the share-weighted 233 chain

Run of 10 November 2026 (one `lean` at a time, `nice -n 10`, oleans in a scratch directory listed
first in `LEAN_PATH`, next to the 234 shard build). This milestone adds new files only.

**Status.** The share-weighted six-centre route of milestones 28 and 31 now has a complete
generic Lean framework, and the real key set `milestones/31-233-cost/data/keys233_best.json.gz`
(tag `B233`) has been run through it:

- The four generic modules compile. Their main theorems use only `propext`, `Classical.choice`
  and `Quot.sound`.
- A toy instance compiles end to end without `sorry`. Its certificates and floors are premises:
  `upper_254_of_refuted6SToy : AllRefuted6SToy → AllRefutedShare6SToy → Floors233 → m ≤ 254`.
- On the real set, the generator reproduces λ = 520/1, a 10-bit potential with range 784 of 1023,
  and the bound 233 (`4720 m ≤ 1104463`). The Python re-check passes on all 10,404,288
  transitions (34 shapes, every label below 9, 6^6 counts).
- In scratch, the following real modules compiled:
  - the keys, data, bridge and aggregate modules. The bridge holds the full k6, H8 and share
    covers, with no `sorry`;
  - 9 of the 204 shards.

  The Sequence and aggregate were built with 3 real shards and 201 `sorry` stubs (6 more real
  shards were compiled afterwards for timing), and with them the chain composes to
  `upper_233_of_refuted6SB233`. A scratch `UpperBound233` with the three certificate
  obligations stubbed gives `upper_bound_233 : ∀ snake, m ≤ 233`. `sorry` enters only through
  those stubs: grep finds it in no other file, and the real shards and the bridge print the
  standard axioms only.

**Update, 10 November: the conditional 233 is Lean-checked.** The production build (section
[Production build](#production-build-of-the-conditional-233-10-november)) compiled every module of the
B233 chain for real, with no stub: the 204 shards, the data, keys, Sequence, bridge and aggregate.
`chain_audit.py` prints

```
'Snake9.upper_233_of_refuted6SB233' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(`outputs/aggregate-233-conditional-chain-linux.log`). Its only premises are the certificate
obligations `AllRefuted6SB233`, `AllRefutedShare6SB233` and the floors `Floors233`.
**233 is now unconditional** (see [Unconditional 233](#unconditional-233)).

**Update, 10 November (later): `Floors233` is discharged.** Main's 1,042 floor modules (commit `32d14f72`,
fetched by blob sha) were compiled on this branch: 1,044/1,044 modules with the two unbuilt branch modules,
0 failed, 2.3 CPU-hours, 477 MB of `.olean` in tmpfs, peak 6.24 GB. Then `work/spectral/stronger/Floors233Main.lean`
compiles, and `chain_audit.py` prints

```
'Snake9.Floors233Port.floors233' depends on axioms: [propext, Classical.choice, Quot.sound]
'Snake9.Floors233Port.upper_233_of_certs6SB233' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(`outputs/floors233-linux.log`). `upper_233_of_certs6SB233 : AllRefuted6SB233 → AllRefutedShare6SB233 → m ≤ 233`
has only the certificate obligations as premises. Run, provenance and the tmpfs caveat:
[FLOORS.md, "Port run"](FLOORS.md#port-run-10-november-floors233-is-discharged).

**Update, 14 November: 233 is unconditional.** All 3,127 certificates of the two premises are built.
There are 2,637 seed certificates for the plain and H8 keys and 490 share certificates, and each one
consists of a clause-soundness module and a replay module. `UpperBound233.lean` applies
`Snake9.Floors233Port.upper_233_of_certs6SB233` to them, and `chain_audit.py` prints

```
UpperBound233: ok 567s (max child RSS so far 12.61 GB)
'Snake9.upper_bound_233' depends on axioms: [propext, Classical.choice, Quot.sound]
'Snake9.verified_interval_191_233' depends on axioms: [propext, Classical.choice, Quot.sound]
# chain wall time 761s; exit 0
# AXIOM AUDIT PASSED
```

(`outputs/upper-bound-233-audit-linux.log`, commit `b65d30ca`). The details are in [Unconditional 233](#unconditional-233).

## The chain

| module | side | contents |
|---|---|---|
| `work/spectral/stronger/WindowAutomaton6SDefs.lean` | core | `Tables6S` (`k6 : Tables6`, H8 tree `htree`, share table `sIdx`/`shr`/`sbits`); `shareAt6`, `share6` (the maximum over both orientations), `wforbH8`; **`check6SAt`**, the step test `num + pot(next) ≤ den·(120 s + share6 (c.drop 2) [t1..t4, s]) + pot(current)`, after the k6 windows and the H8 cut; `StepOK6S`, `ShardsOK6S`, `check6S_of_shards`, `stepOK6S_of_trivial`; `step6S_raw`, `w6S`, `Windows6S`, `invariant6S`, **`total_bound6S`**: `num (m-7) ≤ den · Combined.rsum (w6S T d a) (m-7) + (2^bits - 1)`, exactly the premise `htel` of `combined_bound` |
| `work/spectral/stronger/WindowAutomaton6SV2.lean` | core | the witness-driven shard check (design of `WindowAutomaton7V2`): `check6SAtW` reads one 4-bit code per transition. Code 0 is the inequality with the forward share field and 12 the inequality with the reversed one; 1..10 are the k6 windows (forward or reversed) and 11 the H8 cut. The arithmetic uses GMP primitives, and the potential and share rows are `let`-bound. Bridge **`check6SAt_of_W`** (`propext`, `Quot.sound`): a wrong code can only make a check fail |
| `work/spectral/stronger/DirectionWindowBridge6S.lean` | core | `AllRefutedShareList`. The floor statements `ShareFloor16`, `ShareFloor17` and `Floors233`. `ShareOK`, `shareOK_of_refuted` (via `refuted_share_dir`), `shareOK_floor`, `floorLevel`, `keyLevel`. **`ShareCover`** (the `cover6S` of the plan) with `shareCover_rows` and `shareCover_spec`. **`share_window6`**: in either orientation, `share6` of a snake window is at most the share sum of its 5 centres. `share_windows6S` restates it in the shape of `hS5`. The k6 cover by chunks is `cover6_chunks`. H8: `keysOKH8`, `CoverH8`, `coverH8_spec`, `no_forb_H8` (via `refuted_dirH`). Then `direction_windows_core6S` and `AllP` |
| `work/spectral/stronger/AggregateDirection6SConditional.lean` | mathlib | `rsum_eq_sum` (the sum adapter, `Combined.rsum` = `Finset.sum` over `range`); `upper_of_windows6S`, which combines `total_bound6S`, the window bounds, `core_charge_sum_le 12 p` and `countSeq_facts` in `Combined.combined_bound`; **`upper_of_refuted6S`**: `(num + 4200 den) m ≤ 1099800 den + 7 num + (2^bits - 1)` |
| `milestones/28-combined-identities/lean/CombinedShareToy.lean` | core | `Combined.combined_bound`, imported unchanged as the module `CombinedShareToy` |
| `scripts/gen_lean_automaton6s.py` | | keys, Bellman-Ford, packing and decoding, the re-check and witnesses, and the modules `LocalWindowDirKeys6S<T>`, `WindowAutomaton6S<T>Data`, 204 shards and `…Sequence` (`--stub-shards` writes scratch stubs) |
| `scripts/gen_lean_chain6s.py` | | `DirectionWindowBridge6S<T>` (all kernel covers) and `AggregateDirection6S<T>` (`upper_<N>_of_refuted6S<T>`) |
| toy: `data/toy_set6s.json`, `data/auto6s_Toy.json`, `LocalWindowDirKeys6SToy`, `WindowAutomaton6SToy{Data,Sequence}`, `DirectionWindowBridge6SToy`, `AggregateDirection6SToy` | | 5 plain keys, 3 H8 keys, and 7 share fields (4 on floors, 1 of them the reversed share-17 case, plus 3 share keys); zero potential, λ = 120/1 |

The instance theorem (generated, `AggregateDirection6SB233`):

```
theorem upper_233_of_refuted6SB233 (h : LocalWindow.AllRefuted6SB233)
    (hs : LocalWindow.AllRefutedShare6SB233) (hF : DirectionWindow6S.Floors233)
    {m : Nat} (p : Snake m) : m ≤ 233
```

- `AllRefuted6SB233` covers the plain k6 keys and the H8 keys (`Refuted`).
- `AllRefutedShare6SB233` covers the share thresholds (`RefutedShare … 12 (L-1)`).
- Everything else in the hypothesis list of `upper_of_refuted6S` is proved by kernel checks in the
  generated modules. That is `keysOK6`, `Cover6`, `keysOKH8`, `CoverH8`, `ShareCover` and
  `StepOK6S`.

### Endpoint arithmetic

These are milestone 28's constants.

- `combined_bound` gives `(P + 4200 Q) m ≤ 1099800 Q + 7 P + R`.
- With P/Q = 520/1 and R = 2^10 − 1 = 1023, this is `4720 m ≤ 1104463`, so m ≤ 233.99 and the
  bound is 233. The margin is 17, against 4720 for one more step.
- The real range is 784, so the 10-bit field leaves 239 to spare.

### Floor theorems (main's milestones 73, 152, 155)

- **Statements.** `ShareFloor16 shape` and `ShareFloor17` copy, verbatim and with this branch's
  names, the statements of four theorems on `origin/main`:
  - `Snake9.ShareTransfer152.share16` (012032, milestone 152);
  - `Snake9.CatalogueIntegration73.canonical7300`, `canonical7304` and `canonical7306` (012031,
    012304, 012314, milestone 73);
  - `Snake9.CriticalShare155.share17` (012032 with counts (4, ≤4, 4, ≤5, 3) forward or
    (3, ≤5, 4, ≤4, 4) reversed, milestone 155).

  They were read through the GitHub contents API (`ShareComplete152.lean`,
  `CombinedCatalogue.lean`, `ShareComplete155.lean`), because the local `origin/main` ref
  (29 October) predates milestones 73 to 159.
- **Proofs.** Their proofs were **not ported**. They are hundreds of replay modules (milestone 152:
  342 modules; milestone 155: 137 replay modules plus 98 semantics modules) built on main's own
  infrastructure (`ShareFromCore150`, `CriticalShareAdapter154`, …). So `Floors233` is an explicit
  premise of the conditional theorem.
- **Discharging it** needs those modules built on this branch, and a check that main's `Snake`,
  `dsOf`, `canon`, `coreAlpha` and `coreShare` are this branch's. Each field of `Floors233` is then
  the corresponding main theorem.
- **Use in the cover.** `shareOK_floor` turns the floors into window bounds: level 16 on the four
  shapes, level 17 on the 155 counts. Forward lookups use the forward disjuncts. The reversed
  share-17 pattern uses main's reversed disjunct, through `canon (canon ds).reverse` (012032 is its
  own reversed canonical shape). All 23,293 free share fields of the set satisfy
  `L ≤ floorLevel`, which the generator asserts.

## Dry run on the real set (`data/dryrun_B233.json`)

```
python milestones/33-233-lean/scripts/gen_lean_automaton6s.py --set milestones/31-233-cost/data/keys233_best.json.gz \
  --tag B233 --lam 520/1 --bits 10 --expect-range 784 --expect-bound 233 --dry-run      # 4 s
```

| item | value |
|---|---|
| plain k6 keys | 6,794 (1,383 already replayed + 5,411 paid). They form 36 window shapes and 188 exclusion rows, in 19 chunks |
| H8 keys | 262 (8 directions, 6 counts, reversed form) |
| share fields | 23,783, of which 23,293 are on main's floors and **490** are share keys (`RefutedShare … 12 (L−1)`). There are 46 nonzero share rows; the maximum level is 144, so fields are 8 bits |
| product | 264,384 states; Bellman-Ford over 3,282,198 allowed transitions on canonical labels converges in 31 rounds with **range 784** |
| re-check | 10,404,288 transitions, every label below 9. Each transition has its inequality or an excluding window, checked against the decoded masks, H8 codes, share rows and potential |
| witness codes | inequality, forward share: 5,406,024; inequality, reversed share: 425,214; k6 windows: 4,572,780; H8: 270 |

## Scratch build of the real chain (tag B233)

All runs were on one core, next to the 234 build. Times are CPU seconds of the whole `lean` run,
including imports; RSS is the peak resident size, including mapped mathlib oleans for mathlib
modules.

| module | CPU s | peak RSS | note |
|---|---|---|---|
| `LocalWindowDirKeys6SB233` (core) | 52 | 1.50 GB | key lists are `noncomputable def`, 1.0 MB `.olean` |
| `WindowAutomaton6SB233Data` | 4 | 0.34 GB | 1.3 MB source, 2.1 MB `.olean` |
| shards (9 real) | 9.0-12.6 | 0.53-0.57 GB | see below |
| `WindowAutomaton6SB233Sequence` | 37 | 1.40 GB | with 201 stub shards; 52 prefix checks for the shape cover |
| `DirectionWindowBridge6SB233` (core) | 131 | 1.47 GB | **real** k6 cover (188 rows against their chunks), H8 cover, share cover (one declaration per share shape and first count); no `sorry` |
| `AggregateDirection6SB233` (mathlib) | 3 | 2.76 GB | `upper_233_of_refuted6SB233` |

**Shard timing (shard v2 from the start).**

- **Measured.** Nine shards (0_1, 15_3, 33_6, 5_2, 10_4, 20_1, 25_5, 30_2, 12_6) took 9.0 to
  12.6 s and 0.53 to 0.57 GB each; every one prints `propext`, `Quot.sound` only.
- **Model.** About 1 s of import plus 1.5 to 1.6 s per induced label, each label one
  `decide +kernel` over 7,776 transitions.
- **Projection.** The 204 shards hold 1,338 induced (shape, label, first count) checks: about
  **0.65 CPU-hours**, and about 12 MB of `.olean` at about 60 kB per shard. The shard sources are
  50 to 60 kB each, about 11 MB in all, so they are generated and not committed.

Two pitfalls were fixed while building the real bridge:

- One `rcases` over 188 row memberships took 105 s, so the generated modules prove a nested
  conjunction `AllP P [list]` and use `AllP.mem`. With an underscore for `P` in a `show`, the
  elaborator stalls, so `P` is written out.
- The share cover checked per shape reached 3.0 GB, so it is checked per shape and first count
  (`allSym_of6`). The bridge peak is now 1.47 GB.

Repository note: `ShareBridge` and `AggregateDirectionUnconditional` both declared
`Snake9.countSeq_eq_coreAlpha`, so no module could import both. Since 10 November the newer copy, in
`ShareBridge` (20 October; statement with explicit `k` and `k ≤ m`), is
**`countSeq_eq_coreAlpha_le`**. `ShareBridge` had never been built and only
`AggregateDirection6SConditional` imports it, so the audited 235–238 chains (which import
`AggregateDirectionUnconditional`) are byte-identical and were not recompiled.

## Production build of the conditional 233 (10 November)

Run next to one solver agent on 2 cores: at most 2 `lean` processes, `nice -n 10`, RSS cap 2.5 GB for
the shards and 3 GB otherwise. The design is that of the 234 build (`milestones/25-k7-234/lean`). No
existing `.olean` was rebuilt: before each build, `closure()`/`uptodate()` of
`work/guarded_lake_build.py` (core) and the `--reuse` rule of `chain_audit.py` (chain) were simulated,
and only new 233 modules were stale.

**Layout.**

- Core modules, built with `guarded_lake_build.py --direct --trust-mtime --no-ilean` into
  `work/final_lean/.lake/build/lib/lean`:
  - `LocalWindowShareModel`, `LocalWindowShareBridge`;
  - `LocalWindowDirKeys6SB233` (committed);
  - `WindowAutomaton6SB233Data` and the 204 shards. These were generated by
    `gen_lean_automaton6s.py` into a temporary directory, checked against
    `data/shards6s_B233.sha256` and placed in `work/final_lean` with the fixed old mtime 1793232000
    (2026-10-29, as `shard_build7.py`), so a regenerated source can never make a built `.olean`
    stale. They are gitignored and were deleted after the audit.
- Chain modules, built by `chain_audit.py --reuse` into `work/spectral/.verification/chain`:
  - `CombinedShareToy`, through a symlink `work/spectral/stronger/CombinedShareToy.lean` to
    milestone 28's file;
  - `WindowAutomaton6SDefs`, `WindowAutomaton6SV2`, `ShareCharge`, `ShareBridge`,
    `DirectionWindowBridge6S`, `AggregateDirection6SConditional`;
  - `WindowAutomaton6SB233Sequence`, `DirectionWindowBridge6SB233`, `AggregateDirection6SB233`
    (committed, generated by the two scripts).

**Order and figures.** Times are wall seconds per module. RSS is peak resident memory, including the
mapped mathlib oleans for mathlib modules.

| step | modules | time | memory |
|---|---|---|---|
| core: `LocalWindowShareModel`, `LocalWindowShareBridge` | 2 | 0.8 s, 1.5 s | 0.36, 0.47 GB |
| chain: `CombinedShareToy`, `WindowAutomaton6SDefs`, `WindowAutomaton6SV2` (`outputs/window-automaton6s-v2-linux.log`) | 3 | 1 s each | 0.43 GB |
| chain: `ShareCharge`, `ShareBridge`, `DirectionWindowBridge6S`, `AggregateDirection6SConditional` (`outputs/aggregate-6s-conditional-linux.log`) | 4 | 4, 4, 13, 3 s | 2.66 GB |
| core: `LocalWindowDirKeys6SB233` | 1 | 48 s | 1.41 GB |
| core: `WindowAutomaton6SB233Data` | 1 | 4.4 s | 0.31 GB |
| core: shards (detached, `--heavy-jobs 2`) | 204 | 8.7–15.6 s each; **2,489 CPU s** (0.69 CPU-hours), 1,252 s wall | 0.49–0.58 GB |
| chain: `WindowAutomaton6SB233Sequence` | 1 | 39 s | 1.34 GB |
| chain: `DirectionWindowBridge6SB233` | 1 | 129 s | 1.40 GB |
| chain: `AggregateDirection6SB233` | 1 | 3 s | 2.65 GB |

That is 218 new modules: 208 core and 10 chain. The shard `.olean` files take 13.5 MB in all.

The generator reproduced the dry run exactly: λ = 520/1, range 784, 31 rounds, and a re-check of all
10,404,288 transitions. The summary is `data/auto6s_B233.json`. The audit:

```
python3 work/spectral/chain_audit.py --mathlib-dir /home/user/lean-deps/mathlib4 \
  --target AggregateDirection6SB233 --reuse --log outputs/aggregate-233-conditional-chain-linux.log \
  --axioms Snake9.upper_233_of_refuted6SB233 Snake9.WindowAutomaton.stepOK6SB233
```

It compiled only the Sequence, the bridge and the aggregate. The other 167 modules were reused, and
the chain took 173 s of wall time. Both theorems depend on `propext`, `Classical.choice` and
`Quot.sound`. No module printed `declaration uses 'sorry'`, and no generated or edited source
contains `sorry`, `native_decide` or `axiom`.

To rebuild the shards elsewhere, regenerate them with
`gen_lean_automaton6s.py --set milestones/31-233-cost/data/keys233_best.json.gz --tag B233 --lam 520/1 --bits 10`
(into a temporary `--out-stronger`/`--out-core`). Check them with
`sha256sum -c data/shards6s_B233.sha256` and place the data module and the shards in `work/final_lean`
with an old mtime. Restore them in the same way before a later `chain_audit.py` run, because the
audit needs the source of every core module it imports.

## Unconditional 233

Audit of 14 November 2026, commit `b65d30ca`.

**What is proved.** `work/spectral/stronger/UpperBound233.lean` proves

```
theorem Snake9.upper_bound_233 {m : Nat} (p : Snake m) : m ≤ 233
theorem Snake9.verified_interval_191_233 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 233
```

So every snake (induced path) in the 9-cube has at most 233 edges, and **191 ≤ a(9) ≤ 233**. Both
theorems use only `propext`, `Classical.choice` and `Quot.sound`. No module of the chain prints
`declaration uses 'sorry'`. No generated or edited source that still exists contains `sorry`,
`native_decide` or `axiom`; the certificate sources themselves were deleted after building
([Audit](#audit)).

### The chain of theorems

```
upper_bound_233 : Snake m → m ≤ 233                                   (stronger/UpperBound233.lean)
 ├─ Floors233Port.upper_233_of_certs6SB233 : AllRefuted6SB233 → AllRefutedShare6SB233 → m ≤ 233
 │   │                                                                 (stronger/Floors233Main.lean)
 │   ├─ upper_233_of_refuted6SB233 (h) (hs) (hF : Floors233)           (AggregateDirection6SB233)
 │   │    = upper_of_refuted6S on tables6SB233: total_bound6S, the 204 shards (StepOK6S),
 │   │      WindowAutomaton6SB233Sequence, DirectionWindowBridge6SB233 (keysOK6, Cover6, keysOKH8,
 │   │      CoverH8, ShareCover), Combined.combined_bound: 4720 m ≤ 1104463
 │   └─ floors233 : Floors233 = floors233_of_main share16 canonical7300 canonical7304
 │        canonical7306 share17           (main's 1,042 floor modules, ported; FLOORS.md)
 ├─ allRefuted6SB233 : AllRefuted6SB233                    (final_lean/LocalWindowDirUnsat6SB233)
 │    one kernel mergeOK per chunk of dirChunks6SB233 and one for h8Keys6SB233,
 │    sources dirKeysR6SB233 :: dirChunksN6SB233:
 │    ├─ 1,383 reused plain keys       (LocalWindowDirUnsatR6SB233: window modules of the 237, 236, 235 sets)
 │    └─ 5,673 new keys, 5,411 plain + 262 H8  (LocalWindowDirUnsatN6SB233_0 … _14, 400 keys per chunk)
 │         2,637 by their own (seed) certificate, 2,613 by L1, 423 by L2 from a seed (LocalWindowFamilies)
 └─ allRefutedShare6SB233 : AllRefutedShare6SB233          (final_lean/LocalWindowShareUnsat6SB233)
      490 share thresholds RefutedShare (winOf ds) (boundsOf syms) 12 K, each by its own certificate
      (Tags.refutedShare_of_sat; LocalWindowShareUnsat6SB233_0 … _9, 50 keys per chunk)
```

Each certificate `<M>` (prefix `S` for a seed, `T` for a share threshold) is two modules:

- `LocalWindowCnf/<M>`: the packed UNSAT core and its clause soundness. Every core clause follows from
  the snake axioms of the local window model. Seeds use Sat v2 (`LocalWindowTagsW.checkAllT`, with the
  widened bounds of the seed). Share thresholds use `LocalWindowTagsSW.checkAllS` (flat tables,
  totalizers and clause parts checked separately).
- `LocalWindowUnsat/<M>`: the kernel replay of a CaDiCaL LRAT refutation of that core through checker v3
  (`work/final_lean/LratV3.lean`, whose soundness is proved in Lean). It uses `decide +kernel` per
  segment.

CaDiCaL and the CNF generators are not trusted. The LRAT proof is data for the checker, and every core
clause is derived in Lean.

The rest of the chain is unchanged from the conditional build of 10 November: λ = 520/1, a 10-bit
potential of range 784, the 204 v2 shards, the Sequence, bridge and aggregate (section
[Production build](#production-build-of-the-conditional-233-10-november)), and the floor port
([FLOORS.md](FLOORS.md#port-run-10-november-floors233-is-discharged)).

**Cloud builds.** 19 certificates (8 seeds and 11 share thresholds), the largest ones, were built on
cloud worker containers. The repository owner approved this on 14 November. The workers used the
identical toolchain (Lean 4.19.0, commit `6caaee842e94`) and the identical command
(`work/guarded_lake_build.py --direct --trust-mtime --no-ilean`, through
`milestones/33-233-lean/certify/xfer233.py build`). Their sources were generated by the same
`cert233.py` and moved through temporary git branches `xfer/233/<name>`; the built `.olean` files came
back through `xfer/233o/<name>`. `xfer233.py opull` installed each file only after checking its sha256
and the Lean commit. The record is `certify/data/remotebuild6SB233.jsonl`: name, Lean version, seconds,
peak RSS and the sha256 of each file. So for these 19 certificates the kernel check ran on the cloud
worker. Importing a `.olean` does not run the kernel again, so their trust rests on that worker run and
on the hash check (see [Caveats](#audit)).

### Certificates: counts and sizes

| item | value |
|---|---|
| keys of `AllRefuted6SB233` | 6,794 plain k6 keys and 262 H8 keys. 1,383 plain keys are reused, so 5,673 are new |
| seed plan (`certify/data/seeds6SB233.json.gz`) | 2,637 seeds, 2,098 of them widened. 2,613 keys follow by L1 (`refuted_key_of_wide`) and 423 by L2 (`refuted_key_sub`). The plan took 80 s |
| keys of `AllRefutedShare6SB233` | 490 share thresholds, each certified directly (no family lemma for `RefutedShare`) |
| certificates built | **3,127** (2,637 seeds + 490 share): 6,254 modules (`LocalWindowCnf` + `LocalWindowUnsat`), 0 failed in the end. 3,108 were built on this machine and 19 on cloud workers. The total "3,118" in the earlier lines of [CERT-PROGRESS.md](CERT-PROGRESS.md) was a typo for 3,127 |
| replay hints | 3,336,107,358 in all: 2,337,826,384 seeds, 998,280,974 share; 69,839,929 lemmas; the largest single certificate has 38,914,860 hints. The estimate from the cores' recorded hints (`est_hints`) summed to 5.44 G over the 3,108 locally generated certificates, about 1.85 times their replay count |
| clause-soundness modules (`LocalWindowCnf`) | 12.63 h summed per-module time over the 3,108 built locally (seeds 3.26 h, share 9.36 h), at most 403.9 s and 5.30 GB per module; 429.8 MB of `.olean` in all. The times of the 19 cloud-built Cnf modules were not recorded centrally |
| replay modules (`LocalWindowUnsat`) | **209.84 kernel-hours** (summed per-module time; seeds 131.48, share 78.35; 168.08 h built locally and 41.76 h on cloud workers). The largest module took 19,970.5 s and 7.41 GB (`T012304A35346K47`, built on a cloud worker with a larger stack). 8.87 GB of `.olean` (2.66 B per hint) |
| replay sources | about 17.0 GB in all (14.90 GB for the locally built ones, 2.12 GB for the 19 cloud-built ones). Each source was deleted after its module was built, so only the `.olean` files stay |
| production | from 10 November 14:45 UTC to 14 November 15:32 UTC. `prod233.py` ran 114 batches (`nice -n 10`; 2, then 4, then 3 `lean` jobs; RSS caps of 6.5 to 12 GB). From 12 November `pregen233.py` generator workers also ran, on this machine and on cloud workers. The machine's memory limit is a 13.35 GiB cgroup; after an OOM kill with 4 jobs on 14 November at 00:04 the run used 3 jobs. Log: [CERT-PROGRESS.md](CERT-PROGRESS.md), `certify/data/prod6SB233.jsonl`, `certify/data/replay6SB233.jsonl`, `certify/data/remotebuild6SB233.jsonl`, `work/final_lean/.lake/guarded_build_233cert.jsonl` (kept outside git) |
| premise modules | `LocalWindowDirKeysN6SB233`, `LocalWindowDirKeysR6SB233`, `LocalWindowDirUnsatR6SB233` (53 s, 3.28 GB), `LocalWindowDirUnsatN6SB233_0` … `_14` (`_10` … `_13`: 7-15 s and 0.48-0.55 GB each; the others 8-151 s, at most 1.12 GB), `LocalWindowDirUnsat6SB233` (264.8 s, 11.36 GB), `LocalWindowShareUnsat6SB233_0` … `_9` (7-62 s, at most 0.68 GB), `LocalWindowShareUnsat6SB233` (6.3 s, 3.12 GB). `allRefuted6SB233` and `allRefutedShare6SB233` each depend on `propext`, `Classical.choice`, `Quot.sound` (`work/final_lean/.lake/guarded_build_233final.jsonl`). A first build of `LocalWindowDirUnsat6SB233` at the default 10 GB cap was killed, so `post233.sh` ran with `AGG_RSS_CAP_GB=12.5` |

"Kernel-hours" here is the summed wall time of each module's `lean` process, as `guarded_lake_build.py`
records it: the same guarded-build wall-time measure as in the 235 to 238 write-ups. It is not CPU time.
The modules ran 2 to 4 at a time on 4 shared cores, so the per-hint time is higher than the 0.12 ms
measured with 2 jobs on 10 November.

Production problems, all fixed (from `work/final_lean/.lake/guarded_build_233cert.jsonl`, notes and
[CERT-PROGRESS.md](CERT-PROGRESS.md)):

- Two share Cnf modules (`T012034A62436K99`, `T012340A32626K107`) were killed at the 6.5 GB cap, twice
  each. Share modules with cap ≥ 24 now use clause parts of 1,000 literals (500 from cap 60), and both
  then built.
- `LocalWindowUnsat.T012345A36236K87` overflowed the stack in segment 2. Its fix is the cache warm-up
  `gen_lean_lrat_v3.py --warm 32`: the same LRAT then compiled in 49 s. The statement of each `ok<c>` is
  unchanged.
- `LocalWindowUnsat.T012034A66424K15` failed once with "Stack overflow detected" (10 November, 22:36 UTC;
  its source had been generated before the warm-up existed). `prod233.py` deleted and regenerated its
  source, now with 18 warm-up blocks, and the second build passed in 41.9 s.
- `LocalWindowUnsat.T012034A36435K55` and `T012301A24643K15` failed once each (13 November). The guarded
  log records no error text; [CERT-PROGRESS.md](CERT-PROGRESS.md) records both as kills by the
  memory-cgroup OOM killer, with 4 `lean` jobs next to generator workers under the 13.35 GiB limit.
  `prod233.py` regenerated their sources, and both built on a later attempt.
- `LocalWindowUnsat.T012034A46434K39` failed 4 times and `T012304A33436K87` once. The guarded log records
  no error text for these either. [CERT-PROGRESS.md](CERT-PROGRESS.md) identifies two of the
  `T012034A46434K39` failures (13 November 23:05 UTC, and 14 November 00:04 UTC together with
  `T012304A33436K87`) as memory-cgroup OOM kills with 4 jobs; the cause of its other two failures was
  not recorded. `prod233.py` regenerated its source twice. After the switch to 3 jobs both modules
  built (2,995 s and 4.35 GB for `T012034A46434K39`).
- Larger stack for two certificates. They were compiled with the `lean` binary run through a wrapper
  (`/home/user/leanbig.sh`: `ulimit -s unlimited`, then `lean -s 1048576`, a 1 GB thread stack). This
  changes only the stack size, not the checked content or the statement in the `.olean`.
  - `T012304A35346K47` (share). Its earlier run with the 8 MB stack on a cloud worker died with
    "Stack overflow detected. Aborting." after 12,801 s. With the wrapper, on a cloud worker:
    19,970.5 s, 7.41 GB, ok.
  - `S012301A35344` (seed). Its earlier local run with the 8 MB stack failed after 12,089 s with
    "tactic 'decide' failed. internal error: the elaborator is able to reduce the 'Decidable' instance,
    but the kernel is not able to". With the wrapper, locally: 12,360 s, 6.91 GB, ok.

### Toolchain

- Lean **4.19.0** (`/home/user/lean-deps/toolchain/lean-4.19.0-linux`, commit `6caaee842e94`), and
  mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` for the chain modules.
- Checker **v3**: `work/final_lean/LratV3.lean`, generated by
  `milestones/26-replay-efficiency/scripts/gen_lean_lrat_v3.py`, with segments of 60k and `--warm 32`.
- CaDiCaL **2.1.3** (the binary shipped in the Lean toolchain's `bin/`, `cadical --version`), with
  `--lrat --no-binary` and the configurations recorded per certificate in the `producer` field of
  `replay6SB233.jsonl`. It is untrusted.
- Builds: `work/guarded_lake_build.py --direct --trust-mtime --no-ilean` (core) and
  `work/spectral/chain_audit.py` (chain), on Linux, on the incrementally built core.

### Audit

The whole post-production was run by `certify/post233.sh` with `LEAN_BIN=/home/user/leanbig.sh` and
`AGG_RSS_CAP_GB=12.5`:

0. status: every certificate built;
1. `cert233.py final` as a dry run: 0 of the 30 premise modules differ from those in `work/final_lean`;
2. staleness simulation: exactly the expected 23 modules are stale;
3. guarded build of the two aggregates `LocalWindowDirUnsat6SB233` and `LocalWindowShareUnsat6SB233`,
   standard axioms (figures in the table above);
4. floors overlay `/home/user/floors233-lp-final` (28,365 symlinks, 0 dangling);
5. the audit:

```
python3 work/spectral/chain_audit.py --mathlib-dir /home/user/lean-deps/mathlib4 \
  --target UpperBound233 --reuse --extra-lean-path /home/user/floors233-lp-final \
  --log outputs/upper-bound-233-audit-linux.log \
  --axioms Snake9.upper_bound_233 Snake9.verified_interval_191_233
```

- Result: 173 modules, 172 of them reused. `UpperBound233` took 567 s and 12.61 GB, and the chain 761 s
  of wall time.
- `grep -rlE "sorry|native_decide|^axiom"` printed nothing on the generated and edited sources of the
  233 chain that exist (`work/final_lean/LocalWindowDir*6SB233*.lean`,
  `work/final_lean/LocalWindowShareUnsat6SB233*.lean`, `work/spectral/stronger/*6SB233*.lean`,
  `work/spectral/stronger/Floors233*.lean`, `work/spectral/stronger/UpperBound233.lean`) or on the
  fetched floor sources. The certificate sources `LocalWindowCnf/{S,T}*` and `LocalWindowUnsat/{S,T}*`
  were deleted after each build, so they were not grepped after the fact. They are generated from the
  templates in `certify/cert233.py` and `milestones/26-replay-efficiency/scripts/gen_lean_lrat_v3.py`,
  which contain no `sorry`, no `native_decide` and no `axiom` declaration (the only match of the grep
  is `#print axioms` in cert233.py's premise templates).

**Caveats.**

- As for 238 down to 235, the audit was made on Linux only, against the incrementally built core. No
  fresh source-only rebuild has been run.
- The certificate sources were deleted after compilation to save disk. They can be regenerated from the
  committed core JSONs (see below).
- 19 certificates were kernel-checked on cloud workers, not on this machine (see "Cloud builds" above).
  Their `.olean` files were checked by sha256 and Lean commit on installation. An independent re-check,
  for example with `lean4checker`, has not been done.
- Two certificates were compiled with a 1 GB thread stack instead of the default 8 MB (see the list of
  production problems).
- The floor port's `.olean` files are outside the repository (`/home/user/floors233`, from the tmpfs
  `/dev/shm/floors233`), and the audit reads them through the overlay `/home/user/floors233-lp-final`
  ([FLOORS.md](FLOORS.md)).
- The 1,383 reused keys are proved by the window modules of the 237, 236 and 235 sets, imported by
  `LocalWindowDirUnsatR6SB233` (built 10 November, `.olean` mtime 14:40 UTC, and reused unchanged by the
  guarded build of `post233.sh`): 387 `Q`, 361 `R` and 635 `K` windows. Milestone 34 migrated 746 of the
  748 `Q`/`R` windows to checker v3 (same names and theorem statements; 334 of the swaps were before and
  412 after that `.olean` was built, the last on 11 November at 11:57 UTC). The swaps give the new
  `.olean` an old mtime on purpose, so mtimes cannot show which replay is in place. The audit imported
  whatever `.olean` files were at those paths on 14 November: by milestone 34's manifest
  (`milestones/34-replay-migration/data/manifest.jsonl`), the v3 replays for those 746 windows and the
  earlier replays for `R01203A4434`, `R01203A4443` and the 635 `K` windows. The re-audits of 235, 236
  and 237 after the migration have not been run.

### How to reproduce

Everything below runs from the repository root. Regeneration is deterministic up to the CaDiCaL runs.
A key whose output exists is skipped, so every step can be resumed.

1. **Conditional chain and floors.** Build the B233 shards and the chain as in
   [Production build](#production-build-of-the-conditional-233-10-november). Port main's floor modules and
   build the overlay as in [FLOORS.md, "Port run"](FLOORS.md#port-run-10-november-floors233-is-discharged):
   `scripts/fetch_main_floors.py`, then `guarded_lake_build.py`, then
   `scripts/floors_overlay.py /home/user/floors233/.lake/build/lib/lean /home/user/floors233-lp-final`
   (any new directory; `post233.sh` builds it again in step 4).
2. **Libraries.** `LocalWindowCnfPack`, `LocalWindowTagsW`, `LocalWindowTagsSW`, `LocalWindowFamilies` and
   `LocalWindowDirGlue7`, built with `guarded_lake_build.py --direct --trust-mtime --no-ilean`. Copy
   `LocalWindowTagsShare` and `LocalWindowTagsSharePacked` from the floor port, so that both sides import
   the same `.olean` files.
3. **Cores and plan.** The core JSONs are committed (`milestones/10-window-aggregate/data/lean_core_direction_6s/`,
   one per key, CNF checked by SHA256). So is the plan (`certify/data/seeds6SB233.json.gz`). To redo
   them: `nice -n 10 python3 certify/cert233.py cores [--shard i/n]`, then `python3 certify/cert233.py plan`.
4. **Certificates.** Run
   `setsid nohup nice -n 10 python3 certify/prod233.py --jobs 2 --batch-hints 3e7 &` (or `--jobs 3` on a
   machine with free cores; with 13.35 GiB of memory, 4 jobs caused OOM kills). Optionally also run
   `certify/pregen233.py` workers. Each batch writes `LocalWindowCnf/<M>.lean` and
   `LocalWindowUnsat/<M>.lean` (checker v3, `--warm 32`). It then runs a staleness simulation, builds the
   batch under the RSS cap and deletes the built sources. The largest certificates need a cap of about
   12 GB, and `T012304A35346K47` and `S012301A35344` need the `lean` binary run with a larger stack
   (`ulimit -s unlimited; lean -s 1048576`). Check progress with `python3 certify/cert233.py status`: it
   reaches `seed_unsat_built: 2637`, `share_unsat_built: 490`. This takes about 210 kernel-hours plus
   about 13 h for the Cnf modules, and about 9.3 GB of `.olean`.
5. **Premises, overlay and audit.** Run
   `LEAN_BIN=/home/user/leanbig.sh AGG_RSS_CAP_GB=12.5 bash certify/post233.sh`. `LEAN_BIN` (default: the
   toolchain's `lean`) is the `lean` binary of the aggregate build, and `AGG_RSS_CAP_GB` (default 10)
   its RSS cap; both options were added during this run. It runs `cert233.py final` (which writes
   `LocalWindowDirKeysN6SB233`, `LocalWindowDirUnsatN6SB233_<c>`, `LocalWindowDirKeysR6SB233`,
   `LocalWindowDirUnsatR6SB233`, `LocalWindowDirUnsat6SB233`, `LocalWindowShareUnsat6SB233_<c>` and
   `LocalWindowShareUnsat6SB233`), the staleness simulation, the guarded build of
   `LocalWindowDirUnsat6SB233` and `LocalWindowShareUnsat6SB233`, a new floors overlay (it must list the
   new `LocalWindowCnf`/`LocalWindowUnsat` files) and the audit command above. Before it, restore the
   shard and data sources with the old mtime (`sha256sum -c data/shards6s_B233.sha256`).

The figures in this section come from `certify/stats233.py`
(`nice -n 19 python3 -I milestones/33-233-lean/certify/stats233.py .`), run on
`certify/data/replay6SB233.jsonl`, `certify/data/prod6SB233.jsonl` and
`work/final_lean/.lake/guarded_build_233cert.jsonl`, which covers the 3,108 locally built certificates,
and from `certify/data/remotebuild6SB233.jsonl` for the 19 cloud-built ones.

## Plan of the unconditional 233 (10 November, done)

All rows are done; see [Unconditional 233](#unconditional-233). The estimates below are the plan of
10 November: the measured replay hints are 3.34 G (estimate about 3.2 G hints), 209.84 kernel-hours
(estimate 45 to 50 with checker v3) and 9.3 GB of `.olean` (estimate about 8 GB).

| obligation | type | count | estimate (milestone 31) |
|---|---|---|---|
| plain k6 keys, already replayed | `Refuted (winOf ds) (boundsOf syms)` (237/236/235 replays) | 1,383 | reuse |
| plain k6 keys, new | `Refuted` (LRAT replay with checker v3, `LocalWindowTags` clause soundness) | 5,411 (2,133 of them derivable by L1/L2 of `LocalWindowFamilies` from 3,278 seeds) | 2.40 G hints (2.19 G with L1/L2) |
| H8 cuts | `Refuted (winOf ds) (boundsOf syms)` with 6 bounds for 7 interior vertices (as H9 in milestone 25) | 262 | 0.03 G hints |
| share thresholds | `RefutedShare (winOf ds) (boundsOf syms) 12 (L−1)`, the share CNF (`wincert_share`) replayed with `LocalWindowTagsShare`/`…SharePacked` clause soundness | 490 | 0.78 G hints |
| floors | `Floors233`: main's `share16` (152), `canonical7300/7304/7306` (73), `share17` (155), built on this branch; `Snake9.Floors233Port.floors233`, see [FLOORS.md](FLOORS.md) | 5 theorems | **done** (10 November: 1,042 modules of main, 2.3 CPU-hours, 477 MB of `.olean`) |
| shards | `shard6SB233_<i>_<t0>` (generator, `--shards all`) | 204 | **done** (10 November, 0.69 CPU-hours) |
| glue | `LocalWindowDirUnsat6SB233`: `AllRefuted6SB233` from the replays, by `allRefuted_of_merge` and chunk modules. `LocalWindowShareUnsat6SB233`: `AllRefutedShare6SB233`. `UpperBound233`: the scratch file of this run with the stubs replaced | 3 modules | small |

In total that is 6,163 paid certificates, about 3.2 G hints: about 89 kernel-hours at 0.1 ms per hint,
or about 45 to 50 with checker v3, and about 8 GB of `.olean`. After it, audit
`grep -rlE "sorry|native_decide|^axiom"` and `#print axioms Snake9.upper_bound_233`.

The conditional chain has been built (see "Production build" above). What is left:

1. ~~The certificates `AllRefuted6SB233` (5,411 new plain k6 keys and 262 H8 keys; the other 1,383 are
   reused) and `AllRefutedShare6SB233` (490 share keys)~~: done (3,127 certificates).
2. ~~`Floors233`~~: done; `Floors233Main` gives `upper_233_of_certs6SB233` ([FLOORS.md](FLOORS.md)).
3. ~~The glue `LocalWindowDirUnsat6SB233` and `LocalWindowShareUnsat6SB233`, and `UpperBound233`
   applying `Snake9.Floors233Port.upper_233_of_certs6SB233` to them~~: done (audit of 14 November).

## Files

- `scripts/gen_lean_automaton6s.py`, `scripts/gen_lean_chain6s.py`: the generators.
- `certify/`: the certificate driver (`cert233.py`, `prod233.py`, `pregen233.py`, `share233.py`,
  `post233.sh`) and its logs ([certify/README.md](certify/README.md), [CERT-PROGRESS.md](CERT-PROGRESS.md)).
- `certify/stats233.py`: recomputes the certificate figures of [Unconditional 233](#unconditional-233)
  (read-only).
- `certify/xfer233.py`: cloud build transfer (`gen`, `pull`, `build`, `opull`; record
  `certify/data/remotebuild6SB233.jsonl`).
- `work/spectral/stronger/UpperBound233.lean`: `upper_bound_233`, `verified_interval_191_233`.
- `outputs/upper-bound-233-audit-linux.log`: the audit.
- `data/dryrun_B233.json`: the dry-run summary and scratch timings.
- `data/auto6s_B233.json`: the summary of the production generation (read by `gen_lean_chain6s.py`).
- `data/shards6s_B233.sha256`: sha256 of the data module and the 204 shards (not committed, regenerated).
- `data/toy_set6s.json`, `data/auto6s_Toy.json`: the toy instance.
