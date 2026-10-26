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

## The automaton on the Lean side

The plan of `../README.md` §5 is followed, with three changes:

- **H9 table:** a search tree, not a mask table.
  - H9 rows are very sparse: 17,288 keys in 2,001 rows of 7^6 bits. As masks they would be
    48.6 MB of hex.
  - So `Tables7.htree : NTree` holds the base-9 codes `encB 9 (dirs ++ syms) 0` of the H9 keys.
  - `wforbH T ds syms` looks up `canon ds.reverse ++ syms.reverse`, the reversed key form.
  - The cover is one kernel equality: `CoverH`, the in-order list of the tree equals the key
    codes. Hits are decoded by `encB_inj`.
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
| `scripts/gen_lean_automaton7.py` | keys (`k6`/`F`/`H`), tables, full-product Gauss-Seidel Bellman-Ford with the closed-set skip, decode-and-recheck of every transition, modules: Keys (row-aligned chunks), Data (one potential definition per 8-shape), 792 shards, Sequence (`ShapesCover7` split in 203 prefixes of length 6). Shards hold one `decide +kernel` per (label, t1, t2), 1,296 transitions, `check7In2` (default `--split t2`); `--split t1` gives the planned 18,180 declarations of 7,776 transitions |
| `scripts/gen_lean_chain7.py` | `DirectionWindowBridge7<T>` (`keysOK6`, `keysOKH`, `CoverH`, the zero checks with length 8 split in 15 prefixes, one declaration per nonzero row, `Windows7`) and `AggregateDirection7<T>` (`upper_<N>_of_refuted7<T>`) |
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
- **`WindowAutomaton7L417dData`:** 614 s, 0.78 GB, a 35 MB olean.
  - A single definition with all 4,752 potential rows timed out, so the generator writes one
    potential definition per 8-shape.
- **Shards** (`--split t2`):

  | shard | 8-shape | induced labels | declarations | time | memory |
  |---|---|---|---|---|---|
  | (0, 1) | `[0,1,2,0,3,1,0,4]` | 4 of 6 | 144 | 662 s | 0.93 GB |
  | (131, 3) | `[0,1,…,7]` | 7 of 9 | 252 | 917 s | 0.88 GB |

  - That is 3.6–4.6 s per declaration of 1,296 transitions, about 3 ms per transition.
  - With `--split t1`, one declaration of 7,776 transitions took 35 s at 2.9 GB, and shard (0, 1)
    took 634 s at **3.81 GB**, too close to the cap. That is why `t2` is the default.
  - **Estimate for all 792 shards:** 109,080 declarations × about 4.2 s ≈ **125 CPU-hours** at
    under 1 GB each. The plan estimated about 55. The extra cost is the H9 tree and the own-window
    lookups.
- BRIDGE_PLACEHOLDER

## What remains for a real k7 chain

1. **Certificates** for 36,841 keys: 19,553 k6 keys from the pool and 17,288 H9 keys, about
   34 G hints. The disk requirement (`../README.md`) is the blocker. `AllRefuted7L417d` is the
   only hypothesis left.
2. **The 792 shards:** about 125 CPU-hours at under 1 GB each, then `…Sequence`.
   - The Sequence module is generated but not compiled. Its pieces are the same as those of the
     toy and k6 sequences, except for the 203 prefix checks of `ShapesCover7`, which are not
     measured.
   - Possible speed-ups:
     - a hash split of the H9 tree;
     - skipping dead sources before the inner `allSym s`. This is already done: `own7` sits
       outside it.
     - fewer lookups per transition, for example by caching the target potential row.
3. **`AggregateDirection7L417d`** is generated (`upper_234_of_refuted7L417d`) but not compiled. It
   needs the Sequence module.
4. **The unconditional module** (`UpperBound234`: the replays plus the glue) is not generated.
