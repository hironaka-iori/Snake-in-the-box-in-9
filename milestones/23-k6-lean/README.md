# Lean infrastructure for the six-centre (k = 6) direction automaton

Run of 21 October 2026, next to the 236 replay build (one Lean process at a time, `nice 19`,
oleans in the scratchpad). This milestone adds new files only. It does not change any module
that the 236/237 chains or the existing certificates import.

**Status.** The framework is generic in the tables and the key list. Its main theorems are
proved, and their only axioms are `propext`, `Classical.choice` and `Quot.sound`. A toy
instance compiles end to end (`upper_254_of_refuted6Toy`). On a real instance the
generators, the keys module, the data module, the cover check and a sample of the shards
have been compiled. No real k6 bound has been checked yet: that needs the 204 shards and
the LRAT replays of the keys.

## What a k6 automaton is (Lean side)

- **State:** the canonical induced 7-direction shape (34 of them) and 5 lumped counts.
  That is 34 · 6^5 = 264,384 states, the full product, so Lean needs no closed-set argument.
- **Step:** one direction `d < 9` and one count `s`.
  - The windows of 3 to 7 directions ending at the new vertex (2 to 6 counts) are looked up
    in both orientations.
  - Otherwise `num + pot(next) ≤ den·s + pot(current)` must hold.
- **Exclusion rows:** keyed by (window shape, first count), with masks over `symIdx` of the
  other counts. A 7-direction window therefore costs 7^5 bits per row, like a 6-direction
  window in the k5 tables.
- **Potential rows:** keyed by (7-shape, first count).
- **Sequence bound:** `(num + 35 den) m + 6 den ≤ 9171 den + 7 num + (2^bits − 1)`.
  - This is the same constant as in the k5 chain: C = (2^B − 1) + 7P − 6Q.
  - For λ = 4 with 3 bits it gives 39 m ≤ 9200, i.e. m ≤ 235.

## Files

| file | contents |
|---|---|
| `work/spectral/stronger/WindowAutomaton6Defs.lean` (core) | `Tables6`; `wforb6`, `pot6`, `check6At`; `StepOK`, `ShardsOK`; `check6_of_shards`; `allBelow9_of`; `shapesCover_of` (prefix split); `stepOK_of_trivial`; `step6_raw`, `invariant6`, **`total_bound6`** |
| `work/spectral/stronger/DirectionWindowBridge6.lean` (core) | `keyMask6`, `keysOK6`, `rowOK6`, `Cover6`; `cover6_ok` / **`cover6_rows`**; `symIdx_inj`; **`cover6_spec`**; `window_refute6`, `no_forb_window6`; **`direction_windows_core6`** (the analogue of `direction_windows_core5`) |
| `work/spectral/stronger/AggregateDirection6Conditional.lean` (mathlib) | `upper_of_windows6`; **`upper_of_refuted6`**, which takes `AllRefutedList keys`, `keysOK6`, `Cover6` and `StepOK` and gives the inequality above |
| `scripts/gen_lean_automaton6.py` | keys, tables, Bellman-Ford potential on the full product (`--lam P/Q` or `--lam auto`, i.e. Howard), a Python re-check against the decoded tables, and the modules: keys, data, 204 shards, sequence |
| `scripts/gen_lean_chain6.py` | the bridge instance (`keysOK6`, `Cover6` row by row, `Windows6`) and `AggregateDirection6<T>` (`upper_N_of_refuted6<T>`) |
| `scripts/gen_checker_variants_o5k.py` | `LratCheckO5k`, `LratFastO5k{14..17}`, `LratFast2_O5k{14..17}`, `LratFast2F_O5k{14..17}` in `work/final_lean` (with lakefile entries) |
| `scripts/gen_lean_lrat_o5k.py` | `gen_lean_lrat.py` with `--off 5000`; `--selftest DIR` writes a CNF over the variables 4500 and 4999 |
| toy: `data/toy_keys6.json`, `data/auto6_Toy.json`, `LocalWindowDirKeys6Toy`, `WindowAutomaton6Toy{Data,Sequence}`, `DirectionWindowBridge6Toy`, `AggregateDirection6Toy` | 5 keys, 3 of them six-centre. `upper_254_of_refuted6Toy : AllRefuted6Toy → m ≤ 254` (zero potential, λ = 1) |

### Notes on the checker variants

- There is no 13-bit O5k fast checker. A literal word is `bit + 1 ≤ 10000`, so it needs
  14 bits.
- `NatPack` stores a width per chunk, so it needs no variant.

## How to compile

Each module is compiled by itself with `lean -o`.

- **Core modules:** set `LEAN_PATH` to `work/final_lean/.lake/build/lib/lean`, plus
  `~/lean-deps/chain` for the stronger-side core oleans, plus your output directory.
- **Mathlib modules:** also add the mathlib build and package directories, as in
  `work/spectral/chain_audit.py`.

The order is:

1. `WindowAutomaton6Defs`
2. `DirectionWindowBridge6`
3. `AggregateDirection6Conditional`
4. `LocalWindowDirKeys6<T>`
5. `WindowAutomaton6<T>Data`
6. the shards
7. `…Sequence`
8. `DirectionWindowBridge6<T>`
9. `AggregateDirection6<T>`

Memory figures below are anonymous RSS. Mathlib modules also map about 2.4 GB of olean files.

## Tests run

- **O5k self-test:** the kernel replay of the 4-clause CNF over the variables 4500 and 4999
  compiled through `LratFast2_O5k14`, including a checkpoint (`cpZ`). Its axioms are the
  standard three.
- **Toy chain:** compiled end to end, as listed above.
- **The 237 key set lifted to k6** (`direction_certificates_r4b.json`, 387 certified keys,
  λ = 51/14, run in the scratchpad):
  - The generator finds a 6-bit potential (range 61) in 6 s, re-checks all 6,437,262
    transitions, and gives the bound **237**. That matches the k5 chain.
  - `DirectionWindowBridge6R4bLift` (the real cover) compiles: 25 s, 0.6 GB.
  - Shards (0, 1) and (33, 6) compile with all 9 labels: 114 s and 111 s, 1.87 GB and 1.97 GB.
  - With the shards stubbed, `…Sequence` (52 prefix checks for the shape cover) and
    `AggregateDirection6R4bLift` (`upper_237_of_refuted6R4bLift`) compile. So the generated
    chain composes; only the shard proofs were replaced.
- **Cover cost on 3,103 keys** (the k6_loop A set): about 115 row declarations, 394 s,
  1.15 GB.

## Costs and design choices forced by the 2.5 GB cap

- **Shards:** a k6 step check costs about 1.6× a k5 one per transition, and it needs
  1.9–2.0 GB for a single label. A whole (shape, first count) shard in one declaration would
  pass 4 GB.
  - Each shard file therefore has one `decide` per label, with `Elab.async false`. The
    kernel caches live for one declaration, and the peak stays at 2.0 GB.
  - Estimate: 204 shards × about 2 min ≈ **7 CPU-hours**.
- **Shape cover:** checked in one go it passes 2.5 GB, so it is split into 52 prefix
  declarations (1.1 GB).
- **Cover:** checked row by row (`cover6_rows`).
- **Keys module:** the list is chunked in blocks of 400.

## Finding: the k6_loop key set does not give λ = 4 on the full product

`gen_lean_automaton6.py --lam auto` on `minimal_A_t235.json` + `base_A.json` (3,103 keys,
solver answers) gives:

- a minimum cycle mean of **31/8** on the full product, on an 8-cycle with new counts
  3,3,6,2,6,3,3,5;
- **λ = 4 fails** (there is no potential), and the generated bound would be **236**.

Details are in `data/k6A_full_product.json`.

The k6_loop answer was computed on the lifted live graph of the k5 pickle. The Lean check
covers all 264,384 states. Before a 235 chain exists, one of two things is needed:

- the loop is rerun on the full product, using `transitions()` and Howard from this
  generator, until λ = 4 holds there; or
- a closed-set restriction is formalised.

## What remains for a real k6 chain

1. **A key set that works on the full product.** Rerun the plain loop on the full product
   until λ ≥ 4, then minimise it.
2. **The certificates.** LRAT proofs for every key (CNFs with up to 4,040 variables) go
   through `gen_lean_lrat_o5k.py --off 5000 --wbits 14..17 --fast --split`. The sat/model
   modules then give `AllRefuted6<T>`, as `LocalWindowDirSatR4b` does for the five-centre
   set.
3. **The runs:**
   - `gen_lean_automaton6.py --tag T --lam 4/1` and `gen_lean_chain6.py --tag T`;
   - a guarded build of the 204 shards (about 7 CPU-hours at 2.0 GB each);
   - the cover (minutes);
   - the chain audit.
4. **The unconditional module** (`UpperBound<N>` from the replay modules). It is not
   generated yet.
