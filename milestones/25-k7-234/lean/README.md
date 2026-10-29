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
| `scripts/gen_lean_chain7.py` | `DirectionWindowBridge7<T>` (`keysOK6`, `keysOKH`, `CoverH`, the zero checks with length 8 split in 15 prefixes, one declaration per nonzero row, `Windows7`) and `AggregateDirection7<T>` (`upper_<N>_of_refuted7<T>`) |
| `work/final_lean/LocalWindowDirGlue7.lean` (core) | `AllRefutedSrcs.flatten` (all-refuted chunks give an all-refuted flattened list), `AllRefutedSrcs.cons'`/`nil'`, `allRefutedSrcs_four` |
| `scripts/gen_lean_glue7.py` | `keys`: `LocalWindowDirKeysK7` (+ `_P<i>`), the new keys (in none of `dirKeysR4b`, `dirKeysR4`, `dirKeysK6`) in 93 chunks of 400, `AllRefutedK7 = AllRefutedSrcs dirChunksK7`; `glue`: `LocalWindowDirGlue7<T>`; `final`: `UpperBound<N>` |
| `work/final_lean/LocalWindowDirGlue7L417d.lean` (generated) | **`allRefuted7L417d_of_parts : AllRefuted237 → AllRefuted236 → AllRefutedK6 → AllRefutedK7 → AllRefuted7L417d`**: 111 kernel merges (`mergeOK`), one per chunk of `dirChunks7L417d` (67) and `hChunks7L417d` (44), against the sources `dirKeysR4b :: dirKeysR4 :: dirKeysK6 :: dirChunksK7` |
| `work/spectral/stronger/UpperBound234.lean` (generated) | **`upper_bound_234`**, **`verified_interval_191_234`** from `upper_234_of_refuted7L417d` and the glue applied to `allRefuted237`, `allRefuted236`, `allRefutedK6`, `allRefutedK7` |
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

## What remains for a real k7 chain

1. **Certificates** for the 36,841 new keys (`AllRefutedK7`): 19,553 k6/F8 keys and 17,288 H9 keys,
   about 34 G hints. The disk requirement (`../README.md`) is the blocker. They must end in a
   module `LocalWindowDirUnsatK7` with `allRefutedK7 : AllRefutedK7`.
2. **The 792 shards:** about 160 CPU-hours at 0.9–1.2 GB each (or about 140 with triples).
   - Possible speed-ups, none tried:
     - a balanced skeleton for the H9 spine, instead of a walk of up to 44 nodes;
     - fewer window lookups per transition. The six k6/F8 lookups in both orientations dominate.
3. **Then, in order:** `WindowAutomaton7L417dSequence` (220 s), `AggregateDirection7L417d` (69 s),
   `LocalWindowDirKeysK7` (`gen_lean_glue7.py keys`, 8 minutes), `LocalWindowDirGlue7L417d`
   (6 minutes) and `UpperBound234` (32 minutes, mostly reading 9.9 GB of oleans).

**Imports of the committed modules that are not in the repository yet:**

- `LocalWindowDirGlue7L417d` imports `LocalWindowDirKeys7L417d` (`gen_lean_automaton7.py`) and
  `LocalWindowDirKeysK7` (`gen_lean_glue7.py keys`). Both are generated from the provisional key
  set and are not committed (with the parts, 1.9 MB of source each).
- `UpperBound234` imports `AggregateDirection7L417d` (and, through it, the data, the 792 shards,
  the Sequence and the bridge, all generated) and `LocalWindowDirUnsatK7`, which is not written.
