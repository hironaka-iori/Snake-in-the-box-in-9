## Lean plan for the share-weighted chain to 233

The chain is milestone 23's k6 chain (`WindowAutomaton6Defs`, `DirectionWindowBridge6`,
`AggregateDirection6Conditional`) with one more table, a second certificate type and a different
final identity. Everything below the automaton (the `Refuted` replays, `AllRefutedList`, the
bridges) is reused as it is.

### 1. Automaton (`WindowAutomaton6SDefs.lean`, a copy of `WindowAutomaton6Defs`)

- **`Tables6S`** = `Tables6` plus a share table:
  - `sIdx : Nat → Nat` maps a 6-direction (5-centre) shape code to a row;
  - `shr : Nat → Nat → Nat` maps (row, first count) to packed fields at `cntIdx` of the other
    four counts, in the format of `pot`, holding the level `L`.

  The table holds the levels of `data/keys233_best.json.gz` (`share`, column 3) plus main's floors.
  A field is the maximum over both orientations.
- **`share6 T c t`** looks the trailing 5-window up in both orientations and returns the larger
  value.
- **`check6SAt`** is `check6At` with the step test

  `num + pot6 (c.drop 1) [t1..t4, s] ≤ den * (120 * s + share6 (c.drop 2) [t1..t4, s]) + pot6 (c.take 7) [t0..t4]`.

  The potential uses `B` bits (`B = 10` at `P/Q = 520/1`). The weight needs 13 to 14 bits. Each
  transition costs one more table lookup. The 204-shard layout of `ShardsOK6` stays the same.
- **`invariant6S` / `total_bound6S`** are copies of `invariant6` / `total_bound6`. They give
  `P (m-7) ≤ Q Σ_{n<m-7} (120 sym a(n+7) + S5 n) + (2^B - 1)`.

### 2. Certificates: two types

| type | statement | checker | count (best set) |
|---|---|---|---|
| plain key (k6) | `Refuted (winOf ds) (boundsOf syms)` | the existing LRAT replay (checker v3) and `LocalWindowTags` clause soundness | see README |
| **share threshold (new for this chain)** | `RefutedShare (winOf ds) (boundsOf syms) 12 (L - 1)`: on every fitting window the M = 12 share sum of the 5 centres is at least `L` | the same LRAT replay on the share CNF (`wincert_share`: window + totalizers + `shareCl` + `shareCap`); clause soundness by `LocalWindowTagsShare` / `LocalWindowTagsSharePacked` (`Tags.soundS`, `checkAllS`) | see README |

- The LRAT replay of a share CNF is the same kernel computation as a plain one. Its Cnf/Sat module
  carries the share meaning tree and tags (`mtB64`, `tagsOfS`). A share core is 3 to 5 times
  larger than a plain core (8 k to 38 k clauses; `data/replay233.jsonl`).
- **`cover6S`** is the analogue of `cover6_rows`. Every nonzero field of `shr` at level `L` must
  be backed by one of:
  - (a) a `RefutedShare … 12 (L' - 1)` certificate with `L' ≥ L`, turned into
    `L ≤ Σ_{i<5} coreShare 12 p (r+i+1)` by `refuted_share_dir`
    (`work/final_lean/LocalWindowShareBridge.lean`);
  - (b) for `L ≤ 16` on 012032/012031/012304/012314, or `L ≤ 17` on the milestone-155 counts,
    main's universal floor theorems (milestones 73, 152, 155; their files are on `origin/main`
    and must be brought over).
- Plain keys merge as now, through `allRefuted_of_merge` of the 236/237/235 lists and the new
  chunks. With L1/L2 (`LocalWindowFamilies.lean`), the derived keys are one
  `refuted_key_of_wide` / `refuted_sub` term each.

### 3. Glue: share identity + automaton bound (differs from the k7 234 chain)

The 234 chain ends with the alpha aggregate `sumA (m-1) ≤ 9171 - 35 m`, which is
`countSeq_facts`, and `total_bound7`. The 233 chain replaces it with three pieces.

1. **Window bounds.** For every step n, `S5 n ≤ Σ_{j=n+3}^{n+7} coreShare 12 p j`. This comes
   from `cover6S` and `refuted_share_dir` (or a floor theorem), applied to the snake's window at
   n+2 with its lumped counts.
2. **Share identity.** `core_charge_sum_le 12 p`
   (`work/spectral/stronger/ShareBridge.lean`) gives
   `Σ_{k≤m} (24 coreAlpha p k + coreShare 12 p k) + 840 (m+1) ≤ 221136`.
3. **Combination.** Milestone 28's `combined_bound` (`lean/CombinedShareToy.lean`, core Lean,
   standard axioms) is proved for arbitrary sequences. From the telescoped inequality, the window
   bounds (each 5-window counted once, `window5`), `sym ≤ α`, `4 ≤ α 0`, `4 ≤ α m` and `1 ≤ α j`,
   it derives `(P + 4200 Q) m ≤ 1099800 Q + 7 P + R`. With `P/Q = 520`, `R = 2^10 - 1` this is
   `4720 m ≤ 1104463`, so **m ≤ 233**. The real chain needs one adapter: it replaces `rsum` by the
   project's `Finset.sum` over `Finset.range` (the form `core_charge_sum_le` uses), and identifies
   `sym (a j)` with `symC (coreAlpha p j)` as `upper_of_windows6` does.

So the k7 234 chain has one certificate type (`Refuted`) and an alpha aggregate. The 233 chain
needs:
- a second certificate type (`RefutedShare` with level `L`), with its own clause-soundness tags;
- a share table and `cover6S` in the automaton;
- a final combination step that uses the share identity `core_charge_sum_le` in place of
  `countSeq_facts`.

It needs no H9/F8 windows. The automaton stays k6: 34 · 6^5 states, 204 shards.

### 4. Modules and budget

- Automaton: Keys and Data modules, plus the share table (about 24 k 5-window fields, 5.7 k rows
  at most), 204 shards, Sequence.
  - The shards are the k6 shards with one more lookup: about 6 to 8 CPU-hours (5.9 measured for
    K235).
- Certificates: replays plus Cnf/Sat modules, one per paid certificate (see README for counts,
  hints, kernel hours and `.olean`).
- Glue:
  - `AllRefuted233` (merge of the plain chunks);
  - `AllShare233` (the share certificates by row, plus the floor theorems);
  - `UpperBound233` imports the chain, the glue and `ShareBridge`.
