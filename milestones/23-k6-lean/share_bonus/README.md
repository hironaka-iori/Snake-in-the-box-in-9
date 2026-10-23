# Three-square share bonus on the k6 full product (keys_235)

Run of 23 October 2026, on one core at `nice -n 19`, peak RSS 0.6 GB. This is solver-side and
Python-side only. No Lean module was written or built.

## Answer

**The share bonus does not improve the k6 chain.** Using its exact Lean constants, the bound stays
at **235**, whatever the key set. It also saves no certificate for 235.

| key set | bonus per occurrence | minimum cycle mean of 24 s + bonus | pattern edges on the cycle | bound |
|---|---|---|---|---|
| keys_235 (1,287) | 0, 6, 12, 10,000 | **96** (alpha 4), a 3-cycle with counts 6,1,5 | 0 | 235 |
| all 28,615 known plain UNSAT keys | 0, 6, 12, 10,000 | **195/2** (alpha 4.0625), a 16-walk (period 8) | 0 | 235 |

- **No key set can do better.** Every 6-centre window on the 4.0625 walk is plain SAT at radius 4
  (`obstruction_B6.json`: 78 windows SAT; the 2 untested ones are sub-windows of SAT windows).
  So no plain key of at most 7 directions can remove it. The walk has no 0123415 window, and no
  0123410 window either, so no per-occurrence bonus touches it.
- **The ceiling.** The plain radius-4 k6 abstraction tops out at 4.0625 even with an unbounded
  bonus, and λ' = 195/2 gives m ≤ 235.35.
- **Thresholds for a better bound** (formula below):

  | target | λ' needed | in alpha units |
  |---|---|---|
  | 234 | > 98.95 + (2^b − 1)/228 | 4.123 |
  | 233 | > 103.08 + (2^b − 1)/227 | 4.295 |

  So neither 234 nor 233 can be reached with any number of extra plain keys.
- **No certificate saving.** Pruning from all known keys at λ' = 96 and range ≤ 255 (8 bits)
  gives the same certificate set for B = 0, 6 and 12. That is 635 new certificates, ≈ 294 M
  hints, identical to keys_235 (`prune_b*.json`). Every cycle of mean < 4 that the new keys cut
  is free of the pattern.
- **Why.** Pattern edges do lie on live cycles. With B = −100 there is a 4-cycle with alpha mean
  exactly 4 and pattern density 1/2. But milestone 33's α(r+1) + α(r+6) ≥ 9 already makes those
  cycles expensive, so they are never critical.

## Sound accounting

**Step and window.** Step n of `invariant6` (n = 0 .. m−8) reads the hw6 window, directions
d(n+1) .. d(n+7). Its internal vertices n+2 .. n+7 carry the counts t0 .. t4, s.

**Occurrence.** The edge is a pattern edge iff `canon(x.drop 1) = [0,1,2,3,4,1,5]`. The state
holds the 7-shape and the step direction, so this test is local. With r = n+1 the charged
positions are r+1 = n+2 (count t0) and r+6 = n+7 (the new count s), and r + 7 ≤ m holds.

**V1: 6 per occurrence.** Let J be the set of pattern starts r. Then
6|J| ≤ Σ_{k ≤ m} coreShare 12 k. This is `snake_occurrence_bonus`, or `pair_share_packing`
combined with `pattern_share_in_snake`. It needs nothing beyond the window.

**V2: 12 per matched occurrence.** The charged pairs {r+1, r+6} form paths, since r conflicts only
with r ± 5.
- **Rule.** Credit 12 to r iff r ∈ J and r−5 was not credited. The credited pairs are then
  disjoint, so their sum is ≤ Σ share, and the scheme is exact (12·⌈k/2⌉ per chain).
- **Why it needs state.** Whether r−5 is in J cannot be seen in the 8-direction window. The state
  would have to carry 5 credit bits (×32 states).
- **Not built.** Any per-occurrence scheme credits at most 12 per occurrence. B = 12 without
  state is therefore an upper bound on what V2 can achieve, and it changes nothing (tables above).

## Constants (share-weighted analogue of the k6 form)

**Ingredients.**
- `core_charge_sum_le` with M = 12.
- The endpoint counts are ≥ 4.
- `sumA_ge6` gives the 6 leading counts ≥ 1.
- sym ≤ α.
- The step check is num + pot' ≤ den·(24·sym s + B·[pat]) + pot.

**Bound.** With these,

    den·(24·S6 + 6|J|) ≥ num·(m−7) − (2^b − 1)
    24·(8 + 6 + S6) + 6|J| + 840(m+1) ≤ 221136

and so

    (num + 840 den) m ≤ 219960 den + 7 num + (2^b − 1).

**Check against the alpha-only form.** With B = 0, num = 24P and den = Q, this is the α-only
form (num + 35den)m + 6den ≤ 9171den + 7num + 2^b − 1, multiplied by 24.

**keys_235 in these units.**
- λ' = 96, BF range 120 (7 bits).
- 936 m ≤ 220759, so m ≤ 235.

## What the Lean side would need (not worth doing for this result)

1. **`Tables6` with a bonus.** Add a bonus field to `Tables6`, and a `check6At` variant whose
   weight is 24·sym s + B·[canon (x.drop 1) = PAT]. The shards would have to be regenerated.
2. **Bonus-weighted sequence lemmas.** `step6_raw`, `invariant6` and `total_bound6`, with
   S6 replaced by 24·S6 + B·#{n ≤ m−8 : pattern at n+1}.
3. **An occurrence lemma.** Take J = (range (m−7)).filter pattern, image (+1). Using
   `pattern_share_in_snake` and `pair_share_packing`, get 6|J| ≤ Σ coreShare 12. This needs
   `dir` = `pathDir`, and the canonical-shape test turned into the six distinct coordinates.
4. **Combine.** Put this together with `core_charge_sum_le` (M = 12) and the endpoint and leading
   counts, using the inequality above.

## Files

| file | contents |
|---|---|
| `bonus.py` | minimum cycle mean (Howard) and exact Bellman-Ford of 24 s + B·[pattern] on keys_235 |
| `refine_share.py` | `eval` (all known keys), `loop` (share-weighted plain refinement; it stopped at once on the SAT obstruction), and `prune` (prune.py with the share weight) |
| `obstruction.py`, `obstruction_B6.json` | the 4.0625 walk with the status of each of its windows |
| `results.json`, `prune_b0/b6/b12.json` | the numbers above |
| `oracle_share_bonus.jsonl`, `rounds_share.jsonl` | the 13 plain calls (3 UNSAT) and the 3 rounds of the loop at λ' = 100 |
