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
**No unconditional 233 is checked yet.** That still needs the certificates listed in "Remaining work".

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

## Remaining work for an unconditional 233

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

1. The certificates `AllRefuted6SB233` (5,411 new plain k6 keys and 262 H8 keys; the other 1,383 are
   reused) and `AllRefutedShare6SB233` (490 share keys).
2. ~~`Floors233`~~: done; `Floors233Main` gives `upper_233_of_certs6SB233` ([FLOORS.md](FLOORS.md)).
3. The glue `LocalWindowDirUnsat6SB233` and `LocalWindowShareUnsat6SB233`, and `UpperBound233`
   applying `Snake9.Floors233Port.upper_233_of_certs6SB233` to them.

## Files

- `scripts/gen_lean_automaton6s.py`, `scripts/gen_lean_chain6s.py`: the generators.
- `data/dryrun_B233.json`: the dry-run summary and scratch timings.
- `data/auto6s_B233.json`: the summary of the production generation (read by `gen_lean_chain6s.py`).
- `data/shards6s_B233.sha256`: sha256 of the data module and the 204 shards (not committed, regenerated).
- `data/toy_set6s.json`, `data/auto6s_Toy.json`: the toy instance.
