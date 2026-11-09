# Lean framework for the seven-centre (k7) automaton

Run of 25 October 2026, next to another solver process (one Lean process at a time, `nice -n 10`,
anonymous RSS capped at 4 GB, oleans in the scratchpad). This adds new files only, plus one
lakefile entry. No existing module was changed or recompiled.

**Status.** The framework is generic in the tables and the key lists. Its main theorems are
proved, and their only axioms are `propext`, `Classical.choice` and `Quot.sound`. A toy instance
compiles end to end (`upper_254_of_refuted7Toy`). For the real key set `data/keys_l417d.json.gz`
the generator reproduces the plan of `../README.md` (range 6,377 at 4516/1083, 13 bits, bound
234). It also writes the 792 shards, and the data module and sample shards compile (figures
below). No real k7 bound has been checked yet.

**Update, 29 October.** The whole chain down to `upper_bound_234` and
`verified_interval_191_234` composes, with the 792 shards and the new certificates replaced by
`sorry` stubs in the scratchpad (never committed). Two generator bugs in the Sequence module were
fixed on the way. The glue (`allRefuted7L417d_of_parts`, axioms `propext`, `Quot.sound`) and
`UpperBound234.lean` are committed. Five shards are now measured: the shard build is about
**160 CPU-hours** (fit within 3 % on 4 shards) at 0.9–1.2 GB each, or about 140 with 3 declarations
grouped (2.05 GB). See [the 29 October run](#composition-test-and-glue-29-october).

**Update, 9 November.** Shard v2 (`gen_lean_automaton7.py --shard-v2`): the same 792 shards, checked
through witness codes that pick one disjunct per transition (`WindowAutomaton7V2`, bridge
`check7In_of_W`, axioms `propext`, `Quot.sound`). About **27x faster** on three B234 shards measured
against v1 in the same session (295 → 10.7 s, 718 → 26.7 s, 952 → 34.5 s), about 0.5 GB each and
13 % smaller `.olean`: about **5-6 CPU-hours** for all 792. Same module names and final theorems. See
[Shard v2](#shard-v2-witness-driven-checks-9-november).

## The automaton on the Lean side

The plan of `../README.md` §5 is followed, with three changes:

- **H9 table:** a search tree, not a mask table.
  - H9 rows are very sparse: 17,288 keys in 2,001 rows of 7^6 bits. As masks they would be
    48.6 MB of hex.
  - So `Tables7.htree : NTree` holds the base-9 codes `encB 9 (dirs ++ syms) 0` of the H9 keys.
    The generated tree is a spine (`NTree.spine`) of one balanced subtree per chunk of 400 keys.
  - `wforbH T ds syms` looks up `canon ds.reverse ++ syms.reverse`, the reversed key form.
  - The cover is `CoverH`: the in-order list of the tree equals the key codes. It is checked
    with one kernel equality per chunk (`coverH_spine`), and hits are decoded by `encB_inj`.
- **Potential rows** are keyed by (8-shape, t0, t1), with fields at `cntIdx6 [t2..t5]`: 4,752
  rows of 6^4 fields. One shard declaration (8-shape, label, t0, t1) reads a single source row.
- **Lookups** (`wIdx`, `forb`, `pIdx`, `pot`) are balanced `bif Nat.blt` trees in the generated
  data, not linear `if` chains, so each lookup costs O(log rows).

Everything else is the plan:

- **State:** an 8-direction canonical shape and the counts a2..a7: 132 · 6^6 states.
- **Step:** a label `d ≤ rgsBound shape` and a count s. The tested windows are:
  - the k6 windows of 3..7 directions ending at the new vertex;
  - F8 (`c.drop 1`, 7 counts), both orientations, in the k6 mask table (`T.k6 : Tables6`, so
    `wforb6` and the k6 cover argument are reused verbatim);
  - H9.
- **Closed-set skip:** `own7` (the source state's own k6 windows) skips dead states.
- **Bound:** `(P + 35Q) m + 7Q ≤ 9171Q + 8P + 2^B − 1`.

## Files

| file | contents |
|---|---|
| `work/spectral/stronger/WindowAutomaton7Defs.lean` (core) | `NTree` (`mem`, `toList`, `mem_toList`), `encB`; `Tables7`, `Tables7.k6`, `wforbH`, `pot7`, `own7`, `check7In`, `check7At`; `StepOK7`, `ShardsOK7`, `ShapesCover7`; `isRGS_append`, `allRGS_of_prefixes`, `allBelow_succ_of`, `check7At_of`; **`check7_of_shards`**; `stepOK7_of_trivial`; transport lemmas (`canon_canon_take_drop`, `wforbH_canon`, …); **`step7_raw`** (discharges the skip from the source's own windows); **`own7_false`** (soundness of the skip on a sequence); `Windows7` (= `Windows6` + F8 + H9); `step7`, `invariant7`, `sumA_ge7`, **`total_bound7`** |
| `work/spectral/stronger/DirectionWindowBridge7.lean` (core) | `Cover7` (lengths 3..8), `cover7_ok`, **`cover7_rows`** (row by row, each row against one chunk of keys: `rowOK6_mono`, `mem_flatten_getD`), `cover7_spec`; `keysOKH`, `CoverH`, `encB_inj`, `isRGS_lt`, **`coverH_spec`**; `refuted_extend`, **`refuted_dirH`** (7 bounds on a 9-direction window, the 8th interior vertex unconstrained); `window_refute7`, `no_forb_window7` (3..8); `window_refuteH`, **`no_forb_H9`** (by reversal); **`direction_windows_core7`** |
| `work/spectral/stronger/AggregateDirection7Conditional.lean` (mathlib) | `upper_of_windows7`, **`upper_of_refuted7`** |
| `scripts/gen_lean_automaton7.py` | keys (`k6`/`F`/`H`), tables, full-product Gauss-Seidel Bellman-Ford with the closed-set skip, decode-and-recheck of every transition, modules: Keys (row-aligned chunks), Data (one potential definition per 8-shape), 792 shards, Sequence (`ShapesCover7` split in 203 prefixes of length 6, each checked per 7th digit: 877 declarations). Shards hold one `decide +kernel` per (label, t1, t2), 1,296 transitions, `check7In2` (default `--split t2`); `--split t1` gives the planned 18,180 declarations of 7,776 transitions |
| `work/spectral/stronger/WindowAutomaton7V2.lean` (core; written by `scripts/gen_window_automaton7_v2.py`) | shard v2: `check7In2W`/`check7InW`/`check7AtW` (witness-driven, kernel primitives), **`check7In2_of_W`**, **`check7In_of_W`**, **`check7At_of_W`** (`propext`, `Quot.sound`); `gen_lean_automaton7.py --shard-v2 [t1\|t2\|label]`, `--manifest-out`; manifest `data/shards7_B234_v2.sha256` |
| `scripts/gen_lean_chain7.py` | `DirectionWindowBridge7<T>` (`keysOK6`, `keysOKH`, `CoverH`, the zero checks with length 8 split in 15 prefixes, one declaration per nonzero row, `Windows7`) and `AggregateDirection7<T>` (`upper_<N>_of_refuted7<T>`) |
| `work/final_lean/LocalWindowDirGlue7.lean` (core) | `AllRefutedSrcs.flatten` (all-refuted chunks give an all-refuted flattened list), `AllRefutedSrcs.cons'`/`nil'`, `allRefutedSrcs_four` |
| `scripts/gen_lean_glue7.py` | `keys`: `LocalWindowDirKeysK7` (+ `_P<i>`), the new keys (in none of `dirKeysR4b`, `dirKeysR4`, `dirKeysK6`) in 93 chunks of 400, `AllRefutedK7 = AllRefutedSrcs dirChunksK7` (`--noncomputable`: `noncomputable def`, 15 times smaller oleans); `glue`: `LocalWindowDirGlue7<T>`; `reuse`: the three modules below that replace the old aggregates; `final [--reuse]`: `UpperBound<N>` |
| `work/final_lean/LocalWindowDirGlue7L417d.lean` (generated) | **`allRefuted7L417d_of_parts : AllRefuted237 → AllRefuted236 → AllRefutedK6 → AllRefutedK7 → AllRefuted7L417d`**: 111 kernel merges (`mergeOK`), one per chunk of `dirChunks7L417d` (67) and `hChunks7L417d` (44), against the sources `dirKeysR4b :: dirKeysR4 :: dirKeysK6 :: dirChunksK7` |
| `work/final_lean/LocalWindowDirKeysReuse7L417d.lean` (generated, `reuse`) | the 1,383 keys of the chain that the sets of 237, 236 and 235 prove, in 4 chunks of 400 (`dirChunksReuse7L417d`), `AllRefutedReuse7L417d = AllRefutedSrcs dirChunksReuse7L417d` |
| `work/final_lean/LocalWindowDirUnsatReuse7L417d.lean` (generated, `reuse`) | imports exactly `LocalWindowSat.W` and `LocalWindowUnsat.W` of those 1,383 windows (387 `Q`, 361 `R`, 635 `K`); **`allRefutedReuse7L417d`**, one `refine ⟨Tags.refuted_of_sat W.sat W.unsat, ?_⟩` per key and one theorem per chunk |
| `work/final_lean/LocalWindowDirGlue7L417dReuse.lean` (generated, `reuse`) | **`allRefuted7L417d_of_reuse : AllRefutedReuse7L417d → AllRefutedK7 → AllRefuted7L417d`**: 111 kernel merges against the sources `dirKeysReuse7L417d :: dirChunksK7`; imports key lists only |
| `work/spectral/stronger/UpperBound234.lean` (generated, `final --reuse`) | **`upper_bound_234`**, **`verified_interval_191_234`** from `upper_234_of_refuted7L417d` and `allRefuted7L417d_of_reuse allRefutedReuse7L417d allRefutedK7` (before 29 October, second run: the old glue applied to `allRefuted237`, `allRefuted236`, `allRefutedK6`, `allRefutedK7`; `final` without `--reuse` still writes that form) |
| B234 (final key set, generated, committed): `LocalWindowDirKeys7B234{,_P0..P2}`, `LocalWindowDirKeysK7{,_P0..P2}`, `LocalWindowDirKeysReuse7B234`, `LocalWindowDirUnsatReuse7B234`, `LocalWindowDirGlue7B234Reuse` (work/final_lean); `WindowAutomaton7B234Sequence`, `DirectionWindowBridge7B234`, `AggregateDirection7B234` (work/spectral/stronger); `data/auto7_B234.json` | the chain of `../data/keys_best234.json.gz`; the data module and the shards are regenerated (`data/shards7_B234.sha256`) |
| `scripts/shard_build7.py`, `scripts/build_shards7.sh` | the production build of the data module and the shards in work/final_lean on a small disk: `prepare` (generate, check against the manifest, place with a fixed old mtime; `--restore` places all sources, e.g. before `chain_audit.py`), `stale` (staleness simulation with `guarded_lake_build.py`), `sweep` (deletes built sources, pauses below 250 MB free), `status`; the driver runs batches of `guarded_lake_build.py --direct --no-ilean --trust-mtime` |
| toy: `data/toy_keys7.json`, `data/auto7_Toy.json`, `LocalWindowDirKeys7Toy`, `WindowAutomaton7Toy{Data,Sequence}`, `DirectionWindowBridge7Toy`, `AggregateDirection7Toy` | 5 k6 keys, 1 artificial F8 key and 2 H9 keys. `upper_254_of_refuted7Toy : AllRefuted7Toy → m ≤ 254` (zero potential, λ = 1) |

## How to compile

Each module is compiled by itself with `lean --root=<its directory> -o`. `LEAN_PATH` holds
`work/final_lean/.lake/build/lib/lean`, `work/spectral/.verification/chain` (the 235 chain
oleans, for `WindowAutomaton6Defs`, `DirectionWindowBridge6` and `AggregateDirectionUnconditional`)
and the output directory. Mathlib modules also need the mathlib build and package directories
under `/home/user/lean-deps/mathlib4/.lake`. The wrapper used here was `scratchpad/k7tools/lc.sh`:
it waits for 5 GB of free memory, checks the disk, runs `nice -n 10`, and kills the process by
PID above 4 GB of anonymous RSS.

The order is:

1. `WindowAutomaton7Defs`
2. `DirectionWindowBridge7`
3. `AggregateDirection7Conditional`
4. `LocalWindowDirKeys7<T>_P<j>`, then `LocalWindowDirKeys7<T>`
5. `WindowAutomaton7<T>Data`
6. the shards
7. `…Sequence`
8. `DirectionWindowBridge7<T>`
9. `AggregateDirection7<T>`
10. `LocalWindowDirGlue7`, `LocalWindowDirKeysK7_P<j>`, `LocalWindowDirKeysK7`,
    `LocalWindowDirGlue7<T>`
11. the certificates of the new keys (`LocalWindowDirUnsatK7`, not written yet), then
    `UpperBound<N>`

## What was compiled (25–26 October)

Memory figures are peak anonymous RSS. Mathlib modules also map about 2.4 GB of oleans.

| module | time | memory | axioms |
|---|---|---|---|
| `WindowAutomaton7Defs` | 3 s | 0.1 GB | `check7_of_shards`: the standard three. `step7_raw`, `own7_false`, `total_bound7`: `propext`, `Quot.sound` |
| `DirectionWindowBridge7` | 47 s | 0.15 GB | `cover7_rows`, `coverH_spec`, `refuted_dirH`, `no_forb_H9`, `direction_windows_core7`: the standard three. `coverH_spine`: `propext`, `Quot.sound` |
| `AggregateDirection7Conditional` | 3 s (81 s cold) | 0.23 GB | `upper_of_windows7`, `upper_of_refuted7`: the standard three |
| toy chain (6 modules) | 20 s | 0.34 GB | **`upper_254_of_refuted7Toy`**: the standard three |

**The real key set** (`--tag L417d --lam 4516/1083 --provisional`, generated in the scratchpad,
not committed):

- **Generator.** 20,936 k6 keys and 17,288 H9 keys give 36 window shapes and 202 exclusion rows.
  - 3,130,739 of the 6,158,592 states are live.
  - Of 40,088,093 allowed transitions, all were re-checked against the decoded tables.
  - Bellman-Ford took 21 rounds and found a potential with **range 6,377 (13 bits)**, so the
    bound is **234**. This matches `../README.md`.
  - The run took 19 s in Python.
  - The output is 795 modules: 46 MB of source, including a 21 MB data module.
- **Keys:** 10 part modules of at most 4,000 keys each, 26–37 s and 0.6–0.8 GB each.
  - A single 38,224-key module passed 4 GB and was killed. Elaboration keeps about 1 GB per
    7,000 keys.
- **`WindowAutomaton7L417dData`:** 76 s, 0.57 GB, a 35 MB olean.
  - Two layouts failed or were slow, so the generator writes one potential definition per
    8-shape and one H9 subtree per chunk:
    - a single definition with all 4,752 potential rows timed out in the elaborator after 12
      minutes;
    - with a single 17,288-node H9 tree, the module took 614 s.
- **Shards** (`--split t2`):

  | shard | 8-shape | induced labels | declarations | time | memory |
  |---|---|---|---|---|---|
  | (0, 1), single H9 tree | `[0,1,2,0,3,1,0,4]` | 4 of 6 | 144 | 662 s | 0.93 GB |
  | (131, 3), single H9 tree | `[0,1,…,7]` | 7 of 9 | 252 | 917 s | 0.88 GB |
  | (0, 1), final data (H9 spine) | `[0,1,2,0,3,1,0,4]` | 4 of 6 | 144 | **809 s** | **1.17 GB** |

  - With the single H9 tree, that is 3.6–4.6 s per declaration of 1,296 transitions, about 3 ms
    per transition.
  - The chunked H9 spine, needed for the bridge, costs about 22 % more.
  - With `--split t1`, one declaration of 7,776 transitions took 35 s at 2.9 GB, and shard (0, 1)
    took 634 s at **3.81 GB**, too close to the cap. That is why `t2` is the default.
  - **Estimate for all 792 shards** (superseded by the 29 October measurements below): 109,080 declarations × about 5 s ≈ **150 CPU-hours** at
    about 1.2 GB each (about 125 CPU-hours with a balanced H9 skeleton). The plan estimated about 55. The extra cost is the H9 tree and the own-window
    lookups.
- **`DirectionWindowBridge7L417d`:** 260 s, 1.14 GB. It holds:
  - `keysOK6` and `keysOKH`, per chunk;
  - `CoverH`, as 44 chunk equalities;
  - the zero-row checks;
  - the 202 row declarations against their key chunks.

  **`windows7L417d : AllRefuted7L417d → Windows7 tables7L417d …`** depends only on the standard
  three axioms. The first attempts passed 4 GB, because they checked `keysOK`/`CoverH` in one
  declaration and `rows_ok` hit the recursion depth; hence the per-chunk checks.

## Composition test and glue (29 October)

Run next to solver processes of other agents (load about 4.5 on 4 cores, so the times are upper
bounds). One Lean process at a time, `nice -n 15`, anonymous RSS capped at 4 GB, oleans in the
scratchpad (`k7tools/lc15.sh`). Memory is peak anonymous RSS; the total RSS (which includes the
mapped oleans) is given where it matters.

**Regeneration.** The committed generators (`gen_lean_automaton7.py`, `gen_lean_chain7.py`)
reproduce the scratchpad modules of 25 October byte for byte (data, keys, 792 shards, bridge,
aggregate); only the Sequence changed, by the fixes below.

**Composition test.** The 792 shards were replaced by scratch stubs (the final theorem
`shard7L417d_<i>_<t0>` of each shard, proved by `sorry`; 1–2.5 s and 24 kB each, deleted
afterwards), and so was `LocalWindowDirUnsatK7` (`allRefutedK7 : AllRefutedK7 := sorry`). Then:

| module | time | memory | result |
|---|---|---|---|
| `WindowAutomaton7L417dSequence` (792 imports, 877 + 203 prefix declarations, 132 shape lemmas) | 220 s | 1.70 GB | `stepOK7L417d`, `sorryAx` only through the stubs |
| `AggregateDirection7L417d` | 69 s | 0.23 GB (2.72 GB total) | `upper_234_of_refuted7L417d`, `sorryAx` only through the stubs |
| `LocalWindowDirGlue7` | 2 s | 0.02 GB | standard axioms |
| `LocalWindowDirKeysK7_P0`…`P9` (36,841 keys) | 7–66 s each, 457 s in all | 0.22–0.85 GB | 83 MB of oleans |
| `LocalWindowDirGlue7L417d` (111 kernel merges) | 345 s | 1.84 GB (2.29 GB total) | **`allRefuted7L417d_of_parts`: `propext`, `Quot.sound`**; 24 MB olean |
| `UpperBound234` (imports the R4b, R4 and K6 replays) | 1,906 s, almost all reading oleans | 0.41 GB (**9.9 GB** of mapped oleans) | **`upper_bound_234`, `verified_interval_191_234`**: `sorryAx` only through the stubs |

So the chain composes: once the shards and `LocalWindowDirUnsatK7` exist, `UpperBound234` needs
no other change. The final module maps 9.9 GB of replay oleans; it needs the page cache, not
anonymous memory.

**Generator bugs fixed** (`gen_lean_automaton7.py`, committed):

1. `shapesCover7<T>` and `shardsOK7<T>` turned the membership hypothesis into a disjunction with
   `simp only [List.mem_cons, …]` and split it with `rcases`. On 203 prefixes `simp` hit
   `maxRecDepth` (the k6 sequence had 52). Both are now chains of `refine
   List.forall_mem_cons.2 ⟨…, ?_⟩` (`shapesPres7<T>`, `shardsOK7<T>`).
2. The prefix checks `allRGS 3 (rgsBound pre 0) (shapeTest7 …)` took up to **3.55 GB** in one
   declaration (`[0, 1, 2, 3, 4, 5]`, 504 continuations, 39 s): the Sequence passed 3.6 GB. The
   cost is `inducedPattern` (1.8 GB alone) and the list membership in the kernel; a `Nat.beq`
   membership test was no cheaper. Each prefix is now checked per 7th digit (`shapesPre7<T>_<j>_<a>`,
   at most 72 continuations, at most 0.97 GB) and recombined with `allBelow_succ_of`.

**Glue design.** The new certificates are the keys of `keys_l417d` that are in none of
`dirKeysR4b`, `dirKeysR4`, `dirKeysK6`: 19,553 keys of 5 to 7 directions and the 17,288 H9 keys
(1,383 keys are reused: 387 from 237, 361 from 236 only, 635 from 235). They are kept as 93
chunks of 400 (`dirChunksK7`, sorted like every key list), and the premise is chunked:
`AllRefutedK7 = AllRefutedSrcs dirChunksK7`, so that each chunk can get its own Sat/Unsat
aggregate. The certificate pipeline only has to provide `allRefutedK7 : AllRefutedK7` in a module
`LocalWindowDirUnsatK7`. One kernel merge of the whole key list would not fit: memory grows by
about 16 MB per merge declaration (0.10 GB for one chunk, 0.29 GB for ten, 1.84 GB for all 111),
and needs `Elab.async false` (without it the module passed 4 GB in 2 minutes).

**Shards.** Three more shards, compiled from the final data module:

| shard | declarations | live states (of 7,776) | time | s per declaration | memory |
|---|---|---|---|---|---|
| (0, 1), 25 October | 144 | 4,571 | 809 s | 5.62 | 1.17 GB |
| (3, 6) | 72 | 3,431 | 347 s | 4.82 | 0.90 GB |
| (45, 4) | 180 | 3,770 | 915 s | 5.08 | 1.14 GB |
| (95, 2) | 216 | 3,693 | 1,118 s | 5.17 | 1.10 GB |

- The time is linear in the declarations and the live source states:
  `2.96 s × declarations + 0.58 ms × (live states × labels × 36)`. This fits all four shards within
  3 %.
- Summed over the 792 shards (109,080 declarations, 11.9 M live (state, label) pairs, from the
  generator), this gives **159 CPU-hours**, 5.25 s per declaration on average. Shards take
  3 to 22 minutes, at 0.9 to 1.2 GB each. So three parallel jobs take about 53 hours, and four
  take about 40.
- **Grouping** (12 declarations of shard (45, 4), label 0, t1 = 1, 2, compiled as 12 singles,
  6 pairs, 4 triples or 3 quadruples, each group one `decide +kernel` of a `&&`):

  | group size | time | memory |
  |---|---|---|
  | 1 | 69.6 s | 0.94 GB |
  | 2 | 64.3 s (−8 %) | 1.49 GB |
  | 3 | 61.7 s (−11 %) | 2.05 GB |
  | 4 | 64.5 s (−7 %) | 2.73 GB |

  Memory grows by about 0.55 GB per declaration in a group, and the time saved is about 0.7 s per
  declaration. Pairs (1.5 GB) or triples (2.05 GB, below 2.5 GB) would bring the build to about
  147 or 142 CPU-hours. Quadruples pass 2.5 GB. The generator still writes singles.

## Glue from the window modules (29 October, second run)

Same rules as above (one `lean` at a time, `nice -n 15`, 4 GB cap on anonymous RSS, oleans in a
scratch directory listed first in `LEAN_PATH`, at most 80 MB of new disk). No existing `.olean`
was touched.

**Why.** `UpperBound234` imported the aggregates `LocalWindowDirUnsatR4b`, `…R4` and `…K6`, and
with them every window of the sets of 237, 236 and 235. `gen_lean_glue7.py reuse` writes a glue
that depends only on the windows of the keys the chain takes from those sets.

**Finding: the 234 chain needs every old window.**

- The three sets have 387 + 732 + 635 keys, but `dirKeysR4` shares 371 keys with `dirKeysR4b`,
  so there are 1,383 distinct keys.
- Every one of the 28 key files in `../data` (`keys_l417d`, `keys_l416y`, `keys_l416w`, …)
  contains all 1,383 of them.
- The window oleans on disk are exactly these 1,383 windows: 387 `Q`, 361 `R` and 635 `K`.
- So the new glue imports the same 2,766 window modules as the old aggregates (53,788 oleans in
  all, 21.6 GiB). It frees no disk.
- Only 219 window oleans (0.26 GiB) are not needed: 22 `C` Cnf and 22 `C` Sat modules, and 175
  `D` replays. They are listed in `../certify/unneeded_oleans.txt`, which also gives the disk
  estimate for the full build.

**Design** (`reuse --tag T`; `final --reuse`):

- **`LocalWindowDirKeysReuse7<T>`**: the reused keys, sorted, in chunks of 400
  (`dirChunksReuse7<T>`), and `AllRefutedReuse7<T> = AllRefutedSrcs dirChunksReuse7<T>`.
- **`LocalWindowDirUnsatReuse7<T>`**:
  - it imports exactly `LocalWindowSat.W` and `LocalWindowUnsat.W` for the window W of each
    reused key, read from the `AllUnsat…` conjunctions of the Sat aggregates;
  - one theorem per chunk, with one `refine ⟨Tags.refuted_of_sat W.sat W.unsat, ?_⟩` per key;
  - then `allRefutedReuse7<T>`, by four `AllRefutedSrcs.cons'`.
- **`LocalWindowDirGlue7<T>Reuse`**: the merges of `glue` against the sources `dirKeysReuse7<T>
  :: dirChunksK7`, with tag 0 or 1 + c. It gives `allRefuted7<T>_of_reuse : AllRefutedReuse7<T> →
  AllRefutedK7 → AllRefuted7<T>`.
- All lists in these modules are `noncomputable def`. Measured on part 9 of the K7 keys, the
  compiled code of a key list takes 15 times the space of its definition (2.74 MB against
  0.18 MB). `keys --noncomputable` does the same for `LocalWindowDirKeysK7`.
- The existing glue, the keys output without the flag and the 235–237 chains are unchanged. The
  regenerated `keys`, `glue` and `final` outputs are byte-identical to the earlier ones.

**Compiled** (L417d, peak anonymous RSS; total RSS in brackets when it is mostly mapped oleans):

| module | time | memory | `.olean` | axioms |
|---|---|---|---|---|
| `LocalWindowDirKeysReuse7L417d` | 8 s | 0.20 GB | 0.22 MB | — |
| `LocalWindowDirUnsatReuse7L417d` (2,766 window imports) | 153 s | 0.21 GB (8.50 GB) | 1.52 MB | **`allRefutedReuse7L417d`: `propext`, `Classical.choice`, `Quot.sound`** |
| `LocalWindowDirKeysK7_P0…P9` with `--noncomputable` | 7–34 s each, 291 s in all | 0.20–0.73 GB | **5.6 MB** (83 MB as `def`) | — |
| `LocalWindowDirGlue7L417dReuse` (111 kernel merges) | 369 s | 1.43 GB (1.83 GB) | 0.91 MB (old glue: 24 MB) | **`allRefuted7L417d_of_reuse`: `propext`, `Quot.sound`** |

**Composition test.** The 792 shards and `LocalWindowDirUnsatK7` were scratch `sorry` stubs, as
on the first run (406 s for the 792 stubs).

| module | time | memory | `.olean` | result |
|---|---|---|---|---|
| `WindowAutomaton7L417dSequence` | 234 s | 1.70 GB | 3.8 MB | `stepOK7L417d`: `sorryAx` only through the stubs |
| `AggregateDirection7L417d` | 3 s | 0.22 GB (2.71 GB) | 0.07 MB | `upper_234_of_refuted7L417d`: the same |
| `UpperBound234` (`final --reuse`) | 236 s | 0.37 GB (9.63 GB) | 0.04 MB | **`upper_bound_234`, `verified_interval_191_234`**: `sorryAx` only through the stubs |

So the chain composes as before. The old form took 1,906 s under heavier load. The new form maps
the same replay oleans, so the time difference is not a gain from the design. The committed
`UpperBound234.lean` is now the `--reuse` form, and the three `reuse` modules are committed next
to the old glue. The scratch oleans (45 MB) were deleted.

## Retarget to the final key set (B234, 31 October)

The chain was regenerated for the final key set `../data/keys_best234.json.gz` under the tag `B234`
and composed down to `upper_bound_234` with scratch stubs, as on 29 October. Rules of this run: at
most 3 `lean` processes at a time, `nice -n 10`, at most 2.5 GB RSS for the production shards and
4 GB anonymous RSS for one scratch test at a time, scratch oleans in a directory listed first in
`LEAN_PATH`. No existing `.olean` was touched.

**Generator dry run** (`gen_lean_automaton7.py --keys ../data/keys_best234.json.gz --tag B234 --lam
6423/1544 --noncomputable`, 17 s):

- 7,262 k6/F8 keys (192 F8) and 3,905 H9 keys; 73 window shapes and 268 exclusion rows.
- 3,298,682 of the 6,158,592 states are live. Bellman-Ford took 22 rounds and found a potential of
  **range 8,152 (13 bits)**, so the bound is **234**.
- The Python re-check passed on all **44,649,358** allowed transitions.
- The output matches the partial run of 29 October byte for byte (data module sha256 `6744fe49…`,
  keys, Sequence; `data/auto7_B234.json` differs only in its `seconds` field).
- The L417d outputs regenerate byte for byte after the generator changes of this run
  (`LocalWindowDirGlue7L417d`, `…L417dReuse`, `LocalWindowDirKeysReuse7L417d`,
  `LocalWindowDirUnsatReuse7L417d`, `UpperBound234`). The 235–237 chains were not touched.

**Generator changes** (all optional, defaults unchanged):

- `gen_lean_automaton7.py --noncomputable`: the chain's key lists as `noncomputable def`.
- `gen_lean_automaton7.py --write shards`: write only the selected shards (no 22 MB data module).
- `shard_build7.py` and `build_shards7.sh`: the production shard build on a small disk. See
  `../certify/PROGRESS-B234.md`.
- `work/guarded_lake_build.py --min-disk-mb` (start nothing below that much free disk) and
  `--no-ilean` (with `--direct`: no `.ilean`; on a shard it is 93 kB against 217 kB of `.olean`).

**Compiled.** Every module was compiled for real except the 792 shards and
`LocalWindowDirUnsatK7`, which were `sorry` stubs (scratch only, deleted). Peak RSS is anonymous,
with the total in brackets where mapped oleans dominate. Bridge, reuse and final module ran next to
two production shards, so their times are upper bounds.

| module | time | memory | `.olean` | axioms |
|---|---|---|---|---|
| `LocalWindowDirKeys7B234_P0…P2` (11,167 keys, `noncomputable`) | 21–27 s each | 0.51–0.65 GB | 0.53–0.60 MB | — |
| `WindowAutomaton7B234Data` | 74 s | 0.40 GB | 20.9 MB | — |
| `WindowAutomaton7B234Sequence` | 203 s | 1.70 GB | 3.83 MB | `stepOK7B234`: `sorryAx` only through the stubs |
| `DirectionWindowBridge7B234` | 496 s | 1.18 GB | 4.52 MB | **`windows7B234`**, `cover7B234`: the standard three; `coverH7B234`: `propext`, `Quot.sound` |
| `AggregateDirection7B234` | 2 s | 0.21 GB (2.65 GB) | 68 kB | `upper_234_of_refuted7B234`: `sorryAx` only through the stubs |
| `LocalWindowDirKeysK7_P0…P2` (`keys --noncomputable`: 5,879 + 3,905 = 9,784 new keys, 25 chunks) | 14–27 s each | 0.38–0.67 GB | 0.36–0.63 MB | — |
| `LocalWindowDirKeysReuse7B234` (1,383 reused keys: 387 `Q`, 361 `R`, 635 `K`) | 7 s | 0.22 GB | 0.22 MB | — |
| `LocalWindowDirUnsatReuse7B234` (2,766 window imports) | 1,238 s (I/O bound) | 0.21 GB (8.79 GB) | 1.52 MB | **`allRefutedReuse7B234`: the standard three** |
| `LocalWindowDirGlue7B234Reuse` (21 + 10 kernel merges) | 45 s | 0.47 GB | 0.29 MB | **`allRefuted7B234_of_reuse`: `propext`, `Quot.sound`** |
| `UpperBound234` (`final --reuse --tag B234 --bound 234`) | 212 s | 0.35 GB (11.43 GB) | 41 kB | **`upper_bound_234`, `verified_interval_191_234`: `sorryAx` only through the stubs** |

No real module printed `declaration uses 'sorry'`, and no generated source contains `sorry`,
`native_decide` or `axiom`. So once the shards and `LocalWindowDirUnsatK7` exist, the B234 chain
needs no other change.

**Committed:** the keys (`LocalWindowDirKeys7B234*`, `LocalWindowDirKeysK7*`), the reuse modules,
`LocalWindowDirGlue7B234Reuse`, `WindowAutomaton7B234Sequence`, `DirectionWindowBridge7B234`,
`AggregateDirection7B234`, and the manifest `data/shards7_B234.sha256` (sha256 of the data module
and the 792 shards, which are regenerated by `shard_build7.py prepare`).

**Not committed:**

- The data module (22.6 MB of source) and the shards. They are regenerated byte for byte.
- The B234 form of `UpperBound234.lean` (sha256 `12913755…`). The committed file is still the
  L417d form, as asked. `gen_lean_glue7.py final --reuse --keys ../data/keys_best234.json.gz --tag
  B234 --bound 234` replaces it. The L417d form no longer composes with the committed
  `LocalWindowDirKeysK7`, which now holds the new keys of B234.

**Production shard build.** The build has started: `../certify/PROGRESS-B234.md`. The framework
modules `WindowAutomaton7Defs` (13 s), `DirectionWindowBridge7` (46 s) and
`AggregateDirection7Conditional` are now compiled into `work/spectral/.verification/chain`, by the
invocation of `chain_audit.py`, with the same axioms as on 25 October. The data module and the
shards are compiled into `work/final_lean/.lake/build/lib/lean`.

| shard | `decide`s | time | memory | `.olean` |
|---|---|---|---|---|
| (0, 1) … (0, 6) | 146 | 611–656 s | 1.17–1.25 GB | 217,176 B (+ 92,895 B `.ilean`, now omitted) |

The disk model of `../certify/README.md` (23.7 kB + 1.33 kB per `decide`) predicts 218 kB for these
shards and **167 MB** for all 792 (111,366 `decide`s), without `.ilean`.

## Shard v2: witness-driven checks (9 November)

Study of 9 November 2026 on one core (`nice -n 10`, one `lean` at a time, every module compiled with
`lean -o` into a scratch directory listed first in `LEAN_PATH`, two other agents on the other cores, so
the CPU times are upper bounds). No existing module or `.olean` was touched; the 18 built B234 shards
were only read.

**Result.** `gen_lean_automaton7.py --shard-v2` writes shards that check **about 27 times faster**
(11-35 s instead of 5-16 min per shard; about **5-6 CPU-hours instead of about 160** for the 792
shards) at 0.21-0.24 GB of anonymous memory instead of about 1 GB, with about 13 % smaller `.olean`
files. They keep the module names and the final theorem `shard7<T>_<i>_<t0>` with the same statement,
so the Sequence module, the aggregate and `UpperBound234` are unchanged, and v1 and v2 shards can be
mixed (the 18 built v1 shards stay valid).

### Where the time of a v1 shard goes

Single-theorem probes (`decide +kernel` of one part of `check7In2` over the 1,296 transitions of one
declaration: shard (3, 6), label 0, t1 = 1, t2 = 2; timestamps between theorems), in ms per
evaluation:

| part | ms | note |
|---|---|---|
| whole `check7In2` | 3.9 per transition | 5.0 s per declaration |
| H9 lookup `wforbH` | **4.5** | key `encB 9 (canon ds.reverse ++ syms.reverse)`: 1.9; `NTree.mem` on the spine: 2.4 (one balanced 400-key subtree alone: 1.6) |
| one k6/F8 window `wforb6` (both orientations), 3 to 8 directions | 0.04, 0.11, 0.66, 0.95, 1.07, 1.23 | one orientation of the 8-direction window: 0.51 |
| own windows `own7` (per source state) | 1.9 | |
| step inequality | 0.64 | two `pot7`, the `cntIdx6` list recursion dominates |
| `bif` tree lookups (`wIdx`, `forb`, `pIdx`, potential rows) with a varying key | 0.02 | cheap: they are not the cost |
| `canon` of a varying 7-list | 1.1 | constant ones are cached by the kernel |
| `symIdx` of 6 counts | 0.34 | list recursion (structural recursion through `brecOn`) |
| 8 arithmetic operations on small literals | 0.06 | |

So the kernel time is list recursion (`symIdx`, `cntIdx6`, `List.reverse`, `encB`, `canon`) and the
H9 tree walk, not arithmetic and not the `bif` lookups. The checker evaluates the disjunction in its
order: for every allowed transition all 12 window lookups, the H9 lookup and the inequality, about
10 ms. In shard (3, 6), 29,204 of the 41,916 transitions of live source states satisfy the
inequality (only 7 need H9), and they account for almost all of its 295 s.

### The v2 check

`work/spectral/stronger/WindowAutomaton7V2.lean` (core Lean, imports `WindowAutomaton7Defs`; written
by `scripts/gen_window_automaton7_v2.py`):

- **Witness codes.** `check7In2W T c t0 t1 t2 ws wt` has the loops of `check7In2`, but evaluates
  ONE disjunct per source state and per transition, chosen by 4-bit codes in two literals: per source
  state `(t3, t4, t5)` (216 fields of `ws`) 0 = its transitions, or one of its 10 own windows; per
  transition (1,296 fields of `wt`) 0 = the step inequality, 1..12 = one of the 12 k6/F8 windows
  ending at the new vertex, 13 = H9. A code only selects a disjunct (`bsel4`), so a wrong code makes
  the check fail and can never make it pass. No search, no negative lookup: an allowed transition costs
  one inequality.
- **No list recursion.** The selected disjuncts are written with the kernel's GMP primitives
  (`Nat.add`, `Nat.mul`, `Nat.sub`, `Nat.shiftRight`, `Nat.land`, `Nat.beq`, `Nat.ble`): `fb7` is the
  body of `forbBit6` with the `symIdx` arithmetic unfolded (and the reversed count list written out),
  `ineq7F` is the inequality with the `cntIdx6` arithmetic unfolded and the two potential rows of the
  declaration `let`-bound. The table lookups (`T.wIdx`, `T.forb`, `T.pIdx`, `T.pot`) are those of
  `tables7<T>`; only the H9 disjunct still calls `wforbH` (at most 7 times per shard).
- **Soundness.** `check7In2_of_W : check7In2W T c t0 t1 t2 ws wt = true → check7In2 T c t0 t1 t2 =
  true` for every table, window and codes; `check7In_of_W` and `check7At_of_W` for the grouped forms
  `check7InW` (one `t1`, 6 blocks) and `check7AtW` (one label, 36 blocks). The proof: `bsel4_sound`
  (the selected Boolean is one of the 16), `fb7_eq` with `symIdx_eq1..6` (each selected window is the
  corresponding `wforbA6` disjunct of `wforb6`), `ineq7F_sound` (with `cntIdx4_eq`, equal to the
  inequality of `check7In2`), `src7F_sound` (`own7`), then `allSym_spec`/`allSym_of_forall`. Axioms:
  `propext`, `Quot.sound`. So the kernel still checks, for every transition of the shard, either its
  inequality or one window that excludes it or one own window that excludes its source state.
- **Generator** (`--shard-v2 [label|t1|t2]`, with `--split t2`): `shard_witness` computes the codes
  with numpy from the decoded tables and potential (the same ones the Python re-check uses) and
  asserts that every transition of a live source state with a failing inequality has a window; dead
  source states always take their own window (one lookup instead of six inequalities). Without the
  flag the output is byte-identical to the manifest `data/shards7_B234.sha256`.

### Measurements

All runs on one core next to two other agents, CPU seconds of the whole `lean` run (`wait4`; import
of the data module included), peak RSS with the anonymous part in brackets. v1 and v2 were measured in
the same session. A transition is one (source state, s) pair of a `check7In2` block, 6^4 per
(label, t1, t2): 93,312, 186,624 and 279,936 in the three shards.

| shard | labels | v1 (`check7In2`, 36 `decide`s per label) | **v2, `--shard-v2` (t1, default)** | speed-up | v1 ms/transition | v2 ms/transition |
|---|---|---|---|---|---|---|
| (3, 6) | 2 | 295.4 s, 1.01 GB, 124.6 kB | **10.7 s**, 0.45 GB (0.21), 110.6 kB | **27.5x** | 3.17 | 0.115 |
| (0, 1) | 4 | 718.0 s, 1.24 GB, 217.2 kB | **26.7 s**, 0.46 GB (0.22), 189.1 kB | **26.9x** | 3.85 | 0.143 |
| (95, 2) | 6 | 952.4 s, 1.16 GB (0.92), 312.8 kB | **34.5 s**, 0.48 GB (0.24), 270.7 kB | **27.6x** | 3.40 | 0.123 |
| (100, 1) | 2 | 274-289 s (production log, 3 jobs) | 12.7 s, 0.45 GB (0.21), 110.6 kB | about 22x | | |
| (101, 1) | 5 | 705-723 s (production log, 3 jobs) | 30.8 s, 0.48 GB (0.24), 229.8 kB | about 23x | | |

Repeated runs differ by up to 10 % (95_2: 34.5 and 37.1 s). Every v2 shard theorem depends on
`propext` and `Quot.sound` only.

**Declaration size** (same witnesses, raw `nat_lit` literals):

| one `decide +kernel` per | check | (3, 6) | (95, 2) | anonymous memory |
|---|---|---|---|---|
| (label, t1, t2), 1,296 transitions | `check7In2W` | 12.3 s, 202 kB | 40.9 s, 545 kB | 0.10-0.13 GB |
| **(label, t1), 7,776 transitions** | **`check7InW`** | **10.7 s, 111 kB** | **34.5 s, 271 kB** | **0.21-0.24 GB** |
| label, 46,656 transitions | `check7AtW` | 13.8 s, 88 kB | 40.9 s, 204 kB | 0.99-1.12 GB |

`--shard-v2` defaults to (label, t1); `--shard-v2 label` gives the smallest `.olean` (about 35 % below
v1) at about 1.1 GB.

**Projection for the 792 shards.** The v2 times fit `0.5 s + 5.9 s x induced labels` (5 shards, within
8 %). With 3,030 (shard, induced label) pairs this is **about 5.1 CPU-hours**, or about 5.9 with the
measured 27x applied to the 159 CPU-hours of the v1 fit; 1.7-2 hours of wall time with 3 jobs.
`.olean`: about 0.87 of v1, so about 145 MB instead of 167 MB. Sources: 115-340 kB per shard (v1:
16-46 kB), deleted by the sweeper after the build as before.

### Ideas tried

Probes on shard (3, 6), label 0, (t1, t2) = (6, 6), ms per evaluation in the v2 setting:
inequality 0.11, decoding a code 0.06, dispatch and decoding 0.13, one selected window 0.10, H9 5.6
(used at most 7 times per shard). One declaration of v2 took 0.17-0.23 s against 3.6-5.8 s for v1.

| idea of the task | what was done | speed-up | soundness |
|---|---|---|---|
| per-state transition lists as packed literals | not needed: the window shapes and their codes (`canon`, `shapeCode`, `wIdx`) of a declaration are constant terms that the kernel caches; what costs is evaluating disjuncts that are false | — | — |
| forbidden-transition bitmask / membership certificate | **the witness codes**: per transition the index of the window that excludes it (or 0 = inequality, 13 = H9), per source state its own window; the kernel only evaluates the selected disjunct, never searches and never proves a lookup negative | **about 7.5x** alone (three declarations: 0.45-0.75 s against 3.5-5.5 s for v1) | any code selects one disjunct of the original check (`bsel4_sound`), so a wrong witness fails the check |
| kernel primitives instead of instance arithmetic, `cntIdx6`/`symIdx` unfolded | `Nat.add`/`Nat.mul`/`Nat.shiftRight`/`Nat.land`/`Nat.beq`/`Nat.ble` written directly; dispatch on bits with `Nat.land`/`Nat.beq` instead of `!=`; code 0 tested first | about 3x on top (0.17-0.23 s per declaration); dispatch 0.42 → 0.13 ms, inequality 0.25 → 0.11 ms | `fb7_eq`, `symIdx_eq*`, `cntIdx4_eq`, `nat_beq_eq`, `nat_ble_eq` |
| one packed potential literal per shard | not needed: the two potential rows of a declaration are `let`-bound in `check7In2W` and read once (cached); a lookup in the `bif` trees costs 0.02 ms | — | the rows are `T.pot` itself |
| larger declarations | (label, t1): −15 % time, −50 % `.olean` against (label, t1, t2); per label: slower and 1.1 GB; 36 checks as one `&&` (v1 style grouping): 31 s and 325 kB for (3, 6), worse | 1.15x | `check7In_of_W`, `check7At_of_W` |
| witness literals in separate `noncomputable def`s | 299 kB instead of 227 kB for (3, 6), worse; raw `nat_lit` literals instead: 227 → 202 kB | — | — |

### Composition test

The five v2 shards above (scratch `.olean`, first in `LEAN_PATH`, so for (0, 1), (100, 1) and (101, 1)
they shadow the built v1 shards), the 15 other built v1 shards (read only) and 772 scratch `sorry`
stubs of the remaining shards (121 s in all); the certificates `LocalWindowDirUnsatK7` and
`LocalWindowDirUnsatReuse7B234` were `sorry` stubs too. Everything else was compiled from the committed
sources into the scratch directory; all of it was deleted afterwards (36 MB).

| module | time | memory | result |
|---|---|---|---|
| `LocalWindowDirKeys7B234_P0…P2`, `LocalWindowDirKeys7B234` | 28-33 s each | 0.52-0.66 GB | — |
| `WindowAutomaton7B234Sequence` (792 shard imports, v1, v2 and stubs) | 245 s | 1.96 GB (1.70) | `stepOK7B234`: `sorryAx` only through the stubs |
| `DirectionWindowBridge7B234` | 525 s | 1.53 GB (1.16) | `windows7B234`, `cover7B234`: the standard three; `coverH7B234`: `propext`, `Quot.sound` |
| `AggregateDirection7B234` | 10 s | 2.66 GB (0.21) | `upper_234_of_refuted7B234`: `sorryAx` only through the stubs |
| `LocalWindowDirGlue7`, `LocalWindowDirKeysK7_P0…P2`, `LocalWindowDirKeysK7`, `LocalWindowDirKeysReuse7B234` | 0.2-36 s each | ≤ 0.66 GB | — |
| `LocalWindowDirGlue7B234Reuse` | 50 s | 0.82 GB (0.48) | `allRefuted7B234_of_reuse`: `propext`, `Quot.sound` |
| `UpperBound234` | 3 s | 2.68 GB (0.22) | **`upper_bound_234`, `verified_interval_191_234`: `sorryAx` only through the stubs** |

Exactly the 774 stub modules printed `declaration uses 'sorry'`; every v2 shard theorem
`shard7B234_<i>_<t0>` depends on `propext` and `Quot.sound` only. So the v2 shards drop into the chain
unchanged.

### Production

1. Build `WindowAutomaton7V2` into `work/spectral/.verification/chain` next to `WindowAutomaton7Defs`
   (core Lean, 1-2 s; no `chain_audit.py` target imports it, because the shards are core leaves), e.g.
   `python3 work/spectral/chain_audit.py --mathlib-dir <mathlib> --target WindowAutomaton7V2 --log
   outputs/window-automaton7-v2-<host>.log --axioms Snake9.WindowAutomaton.check7At_of_W
   Snake9.WindowAutomaton.check7In_of_W`.
2. Shards: `SHARD_V2=t1 milestones/25-k7-234/lean/scripts/build_shards7.sh` (the driver passes
   `--shard-v2 t1` to `shard_build7.py prepare`, which checks every source against
   `data/shards7_B234_v2.sha256`). The manifest was written with `gen_lean_automaton7.py --shard-v2
   --manifest-out` (no module written); its data-module line is the v1 one. Shards whose `.olean`
   exists (v1 or v2) are skipped. With about 0.5 GB per shard, the RSS cap can drop to 1 GB and the
   heavy jobs can go up to the core count.
3. Nothing after the shards changes: the Sequence, `AggregateDirection7B234` and `UpperBound234` only
   use the theorems `shard7B234_<i>_<t0>`.

Files: `work/spectral/stronger/WindowAutomaton7V2.lean` (new), `scripts/gen_window_automaton7_v2.py`
(writes it), `scripts/gen_lean_automaton7.py` (`--shard-v2 [t1|t2|label]`, `--manifest-out`),
`scripts/shard_build7.py` (`prepare --shard-v2`), `scripts/build_shards7.sh` (`SHARD_V2`, `MAN`),
`data/shards7_B234_v2.sha256`.

## What remains for a real k7 chain

This list was written for L417d. For the final set B234 the figures are 9,784 new keys and
1.733 G hints (`../certify/README.md`, "Final key set"), and the shard build has started
(`../certify/PROGRESS-B234.md`).

1. **Certificates** for the 36,841 new keys (`AllRefutedK7`): 19,553 k6/F8 keys and 17,288 H9 keys,
   about 34 G hints. The disk requirement (`../README.md`) is the blocker. They must end in a
   module `LocalWindowDirUnsatK7` with `allRefutedK7 : AllRefutedK7`.
2. **The 792 shards:** about 160 CPU-hours at 0.9–1.2 GB each (or about 140 with triples).
   *(9 November: with shard v2, about 5-6 CPU-hours at about 0.5 GB each; see "Shard v2".)*
   - Possible speed-ups, none tried:
     - a balanced skeleton for the H9 spine, instead of a walk of up to 44 nodes;
     - fewer window lookups per transition. The six k6/F8 lookups in both orientations dominate.
3. **Then, in order:** `WindowAutomaton7L417dSequence` (220 s), `AggregateDirection7L417d` (69 s),
   `LocalWindowDirKeysK7` (`gen_lean_glue7.py keys --noncomputable`, 5 minutes),
   `LocalWindowDirKeysReuse7L417d` and `LocalWindowDirUnsatReuse7L417d` (3 minutes),
   `LocalWindowDirGlue7L417dReuse` (6 minutes) and `UpperBound234` (4 to 32 minutes, mostly
   reading 9.6 GB of oleans).

**Imports of the committed modules that are not in the repository yet:**

- `LocalWindowDirGlue7L417d` imports `LocalWindowDirKeys7L417d` (`gen_lean_automaton7.py`) and
  `LocalWindowDirKeysK7` (`gen_lean_glue7.py keys`). Both are generated from the provisional key
  set and are not committed (with the parts, 1.9 MB of source each).
- `LocalWindowDirGlue7L417dReuse` imports the same two modules.
- `UpperBound234` imports `AggregateDirection7L417d` (and, through it, the data, the 792 shards,
  the Sequence and the bridge, all generated) and `LocalWindowDirUnsatK7`, which is not written.
