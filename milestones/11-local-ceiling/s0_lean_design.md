# Adding the corner share `s0` to the Lean pipeline: design

Design note, 20 October 2026.  Read-only analysis of the current chain (bound 236 via
`work/spectral/stronger/UpperBound236.lean`); nothing here is implemented.  Line numbers
refer to the files on branch `research/unconditional-241` at this date.

## 0. Summary

The chain today proves, for a snake with `m` edges and `v = m+1` vertices,

* **geometry:** `T + 35 v ≤ 9214` (`countSeq_facts`, `work/spectral/stronger/AggregateWindowConditional.lean:22-26`, from `global_identity` and `wedge_total_upper`), with `T = Σ_j α_j`;
* **automaton:** `42 m ≤ 11 Σ_{j=1}^{m-1} α_j + 291` (`total_bound5R4`, `work/spectral/stronger/WindowAutomaton5R4Sequence.lean:91-101`), from 732 window exclusions;
* **arithmetic:** `427 m ≤ 101172`, so `m ≤ 236` (`AggregateDirection236Conditional.lean:15-39`).

The share changes each layer as follows.

| layer | today | with the share |
|---|---|---|
| per-vertex charge | `α(x)` | `g(x) = 2M·α(x) + shareN_M(x)`, `shareN_M(x) = Σ_{q ∈ N(x)} ⌊M·e0(q)/d(q)⌋` |
| global inequality | `T + 35 v ≤ 9214` | `Σ_x g(x) + 70 M v ≤ 18428 M` (new, §1) |
| certificate statement | `Refuted W bounds`: no `S,E` with `Axioms` | `RefutedShare W bounds M K`: no `S,E` with `Axioms ∧ shareSum ≤ K` (§2) |
| automaton symbol | `sym α ∈ 1..6` | unchanged (§3.1 explains why a pair symbol is infeasible) |
| automaton edge weight | `sym s` | `W(e) = 10 M·sym s + T5(e)`, `T5` = certified lower bound on the share sum of the 5-centre window ending at `e` (§3) |
| step test | `P + pot' ≤ Q·s + pot` | `P + pot' ≤ Q·(10 M s + shareT5 window syms) + pot` |
| final arithmetic | `(P + 35Q) m ≤ 9171 Q + C` | `(P + 350 M Q) m ≤ 91710 M Q + C` |
| CNF | `wincert.Encoding` | plus the `e1lib.ShareModel` clauses with a static cap (§4) |
| clause soundness | 12 tag families | plus 5 families and 3 variable meanings (§4.2) |

With `M = 12` (exact for `d ∈ {1,2,3,4,6}`, `s0_radius4/README.md`) the units are
`g = 24 α + shareN` and the final inequality is `(P + 4200 Q) m ≤ 1100520 Q + C`.  A
share-weighted mean `λ = P/Q = 120 μ` corresponds to a charge mean `μ` in α-units and gives
`m ≤ 9171/(μ + 35)`: `μ = 4.76` gives 230, `μ = 4.3` gives 233, `μ = 42/11 = 3.82` gives 236.

The expected gain (`s0_radius4/README.md`): single-centre shares alone move the mean to
3.933 (236.66, no gain); pairs and triples to 3.87-4.0 (still 236); five-centre windows
plausibly to 4.6-4.77 (231-230).  So the first Lean-checked improvement needs the
five-centre share certificates and a converged share-aware refinement (§5).

## 1. Lean: the global inequality

**File:** new `work/spectral/ShareCharge.lean` (mathlib, imports `SquareIncidence`), or
appended to `work/spectral/SquareIncidence.lean` after `wedge_total_upper` (`:231`).  A
separate file keeps the audited 254 file untouched.

**Definitions** (all in `namespace Snake9.SquareIncidence`, reuse `flip` `:16`,
`selected` `:66`, `singleton` `:68`, `empty` `:75`, `AxisPair` `:12`, `Coord` =
`Fin 9` from `work/final_lean/CubeLocal.lean:7`):

```lean
/-- Empty squares containing `q` (`empty` is anchored at every corner, so this is
`e0(q)`); zero when `q` is selected. -/
def emptyAt {m : Nat} (p : Snake m) (q : Vertex) : Nat := ∑ ab : AxisPair, empty p ab q

/-- Selected neighbours `d(q)`. -/
def selDeg {m : Nat} (p : Snake m) (q : Vertex) : Nat := ∑ k : Coord, selected p (flip k q)

/-- Integer corner share of resolution `M` received by `x` from its nine neighbours
(a selected neighbour contributes `0` because `emptyAt` vanishes there; `d(q) = 0`
gives `0` by `Nat.div`). -/
def shareN {m : Nat} (M : Nat) (p : Snake m) (x : Vertex) : Nat :=
  ∑ k : Coord, M * emptyAt p (flip k x) / selDeg p (flip k x)
```

Note that no "q unselected" guard is needed: `empty p ab q` requires `¬ InPath p q`
(`:75-77`), so `emptyAt p q = 0` for selected `q`.  This also matches the local model
(§2) and the CNF (§4), which sum over the 7 non-path neighbours only: the two path
neighbours contribute `0` on both sides.

**Theorems to prove** (names proposed):

```lean
theorem emptyAt_total {m} (p : Snake m) : (∑ q, emptyAt p q) = totalEmptyAnchored p
-- unfold totalEmptyAnchored (:108); Finset.sum_comm

theorem share_double_count {m} (M : Nat) (p : Snake m) :
    (∑ x, selected p x * shareN M p x) =
      ∑ q, selDeg p q * (M * emptyAt p q / selDeg p q)
-- Σ_x sel(x) Σ_k f(flip k x) = Σ_k Σ_x sel(x) f(flip k x) = Σ_k Σ_q sel(flip k q) f(q)
-- (sum_flip :34 with flip_twice :18, per coordinate k), then Finset.sum_comm again.

theorem share_total_le {m} (M : Nat) (p : Snake m) :
    (∑ x, selected p x * shareN M p x) ≤ M * totalEmptyAnchored p
-- share_double_count, Nat.div_mul_le_self per q (d * (M e0 / d) ≤ M e0), emptyAt_total.

/-- The weighted incidence inequality: `Σ_x (2M α(x) + shareN(x)) + 70 M v ≤ 18428 M`. -/
theorem charge_total_le {m} (M : Nat) (p : Snake m) :
    (∑ x, selected p x * (2 * M * (∑ ab : AxisPair, singleton p ab x) + shareN M p x))
      + 70 * M * (m + 1) ≤ 18428 * M
```

Proof of `charge_total_le`: `Σ_x selected x * Σ_ab singleton p ab x = totalSingleton p`
(singleton is `0` at unselected `x`; `Finset.sum_comm` as in `singleton_total_lower`
`:149-159`); `global_identity` `:110-112` (`2·TEA + 4T + 144 v = 36864 + 4W`),
`wedge_total_upper` `:231` (`W ≤ m-1`), `selected_total` `:120` (`v = m+1`) give
`TEA + 2T + 70 v ≤ 18428`; multiply by `M`, add `share_total_le`; `omega`/`nlinarith`
with `M` as a variable (linear in the sums once `M*TEA` is a single atom; use
`Nat.mul_le_mul_left` explicitly).  For `M = 12` everything is linear.

**Path-indexed form** (the shape the automaton consumes), in a new mathlib module next
to `AggregateWindowConditional.lean` (which defines `countSeq` `:15` and `psum` from
`WindowPotential242.lean:146`):

```lean
def shareSeq {m : Nat} (M : Nat) (p : Snake m) (k : Nat) : Nat :=
  if hk : k < m + 1 then shareN M p (p.vertex ⟨k, hk⟩) else 0

/-- Mirrors `countSeq_facts` `:22-26`; the endpoint lower bounds `4 ≤ countSeq p 0`,
`4 ≤ countSeq p m` are reused from there (`endpoint_alpha_ge_four`,
`work/spectral/stronger/UpperBound247.lean:22`). -/
theorem charge_facts {m : Nat} (M : Nat) (p : Snake m) (hm : 3 ≤ m) :
    2 * M * (countSeq p 0 + psum (fun j => countSeq p (j+1)) (m-1) + countSeq p m)
      + (shareSeq M p 0 + psum (fun j => shareSeq M p (j+1)) (m-1) + shareSeq M p m)
      + 70 * M * (m + 1) ≤ 18428 * M
```

Proof: as `countSeq_facts`, with `Σ_x selected x * f x = Σ_{i : Fin (m+1)} f (p.vertex i)`
proved like `selected_total` `:120-128` (image of the injective `p.vertex`) and
`totalSingleton_eq_path_sum` (`AggregateSingletonBound.lean:16`).

## 2. Lean: the local model and the bridge

### 2.1 Local definitions (`work/final_lean/LocalWindowModel.lean`, core Lean)

Reuse `nbrs` `:24`, `cnt` `:27`, `freePairs` `:30` (`freePairs 9 9` is all 36 pairs,
`freePairs k k` the 28 pairs avoiding `k`), `Centre` `:40`, `Axioms` `:50-64`.

```lean
/-- The square at `q` spanned by `ab` has no selected corner. -/
def emptyPred (S : Nat → Bool) (q : Nat) (ab : Nat × Nat) : Bool :=
  !S q && !S (q ^^^ (1 <<< ab.1)) && !S (q ^^^ (1 <<< ab.2)) &&
  !S (q ^^^ (1 <<< ab.1) ^^^ (1 <<< ab.2))

/-- `e0(q)` over all 36 pairs (mirrors `emptyAt`). -/
def emptyCount (S : Nat → Bool) (q : Nat) : Nat := ((freePairs 9 9).filter (emptyPred S q)).length

/-- `shareN_M(x)` over the nine neighbours (mirrors `shareN`). -/
def shareLocal (M : Nat) (S : Nat → Bool) (x : Nat) : Nat :=
  ((List.range 9).map fun k =>
    M * emptyCount S (x ^^^ (1 <<< k)) / cnt S (nbrs (x ^^^ (1 <<< k)))).sum

def shareSum (M : Nat) (S : Nat → Bool) (cs : List Centre) : Nat :=
  (cs.map fun c => shareLocal M S c.v).sum

/-- `Axioms` plus a cap on the window's share sum.  A certificate refutes the cap. -/
structure AxiomsS (S E : Nat → Bool) (window : List Nat) (centres : List Centre)
    (M cap : Nat) extends Axioms S E window centres : Prop where
  share_le : shareSum M S centres ≤ cap

def RefutedShare (window : List Nat) (bounds : List (Nat × Nat)) (M cap : Nat) : Prop :=
  ∀ S E : Nat → Bool, AxiomsS S E window (centresOf window bounds) M cap → False
```

`Refuted W b` (`:102`) implies `RefutedShare W b M K` for every `K` (forget
`share_le`), so the 732 existing certificate modules and `AllRefuted236` stay valid
without regeneration; the existing exclusion tables and `DirectionWindowBridge5R4`
are untouched.  `RefutedShare` is a separate key list and table (§3.2).

The alpha bounds of a share certificate are the same lumped bounds `boundsOf syms`
(`LocalWindowDirModel.lean:27-29`) as the exclusions, exactly as `e1lib` ran them
(`(6, 21)` for the symbol `6`).

### 2.2 What the bridge must prove (`LocalWindowBridge.lean`, `LocalWindowDirBridge.lean`)

The frame `amap P t v = π(v ⊕ t)` (`:195`) maps squares to squares and neighbourhoods
to neighbourhoods, so every share quantity is frame-invariant.  New theorems, with the
existing ones they copy:

| new theorem | statement | copies |
|---|---|---|
| `emptyPred_frame` | `emptyPred (sel p (amap P t)) (amap P t q) (P.fwd a, P.fwd b) = emptyPred (sel p id) q (a, b)` for `t, q < 512`, `a, b < 9` | `singPred_frame` `:447-454` (uses `amap_flip` `:199`, `sel_amap` `:433`) |
| `emptyCount_frame` | `emptyCount (sel p (amap P t)) (amap P t q) = emptyCount (sel p id) q` | `singCount_frame` `:508-527` (`filter_length_le` `:58`, `sorted_mem_inj` `:464`, `sorted_mem` `:486`); also needs `emptyPred_symm`/`emptyPred_sort` as `singPred_symm` `:422`, `singPred_sort` `:441` |
| `cnt_nbrs_frame` | `cnt (sel p (amap P t)) (nbrs (amap P t q)) = cnt (sel p id) (nbrs q)` | new: write `cnt S (nbrs v) = ((List.range 9).filter (fun k => S (v ^^^ 2^k))).length` (`mem_nbrs` `:327`, `nbrs_nodup` `:341`), then reindex `k ↦ P.fwd k` with `filter_length_le` in both directions as in `singCount_frame` |
| `shareLocal_frame` | `shareLocal M (sel p (amap P t)) (amap P t x) = shareLocal M (sel p id) x` for `t, x < 512` | sum over `k < 9` reindexed by `P.fwd` (a permutation of `range 9`: `List.Perm` of the mapped list, `List.Perm.sum_eq`), with `amap_flip`, `emptyCount_frame`, `cnt_nbrs_frame` |
| `coreShare` | `def coreShare (M) (p : Snake m) (k : Nat) : Nat := shareLocal M (sel p (fun v => v)) (vx p k)` | `coreAlpha` `:420` |
| `shareSum_window` | `shareSum M (sel p (amap P (vx p r))) (centresOf W bounds) = ((List.range bounds.length).map fun i => coreShare M p (r+i+1)).sum` under `Canon W cs`, `hP` | the `alpha` case of `frame_axioms` `:830-855` (`frame_window` `:725`, `centresOf` `:87`) |
| `frame_axiomsS` | `AxiomsS (sel p (amap P (vx p r))) (frameE p P (vx p r)) W (centresOf W bounds) M (Σ_i coreShare M p (r+i+1))` | `frame_axioms` `:748` for `toAxioms`; `share_le` is `le_refl` after `shareSum_window` |
| `refuted_share_bridge` | `RefutedShare W bounds M K → … → K + 1 ≤ ((List.range bounds.length).map fun i => coreShare M p (r+i+1)).sum` | `refuted_bridge` `:858`: `Nat.lt_of_not_le` on `share_le` |
| `refuted_share_dir` | same with `winOf cs`, `boundsOf syms`, the relabelling list `u`, conclusion `K + 1 ≤ ((List.range syms.length).map fun i => coreShare M p (r+i+1)).sum` | `refuted_dir` (`LocalWindowDirBridge.lean:90-108`) |
| `coreShare_rev` | `coreShare M (revSnake p) k = coreShare M p (m - k)` for `k ≤ m` | `coreAlpha_rev` `:900` (`sel_rev` `:889`, `vx_rev` `:884`) |

Nothing about the ball radius enters: the radius only decides which CNF variables
exist, exactly as for the 236 set (`milestones/10-window-aggregate/README.md`,
"Radius 4").  `shareLocal` reads `S` at distance ≤ 3 from `x` (neighbour `q`, its
squares, its neighbours), so a window with 5 centres at radius 4 contains everything
the share needs; at radius 3 the squares of `q` sit on the boundary, which is why the
share is free there (`s0_corner_charge.md`, §1).

**Identification with the mathlib side** (new theorem next to
`localAlpha_eq_coreAlpha`, `work/spectral/stronger/AggregateWindowUnconditional.lean:35`):

```lean
theorem shareN_eq_coreShare {m} (M : Nat) (p : Snake m) (k : Nat) (hk : k < m + 1) :
    shareN M p (p.vertex ⟨k, hk⟩) = LocalWindow.coreShare M p k
-- inPath_iff_sel (:19), emptyAt ↔ emptyCount through the AxisPair/freePairs 9 9 bijection
-- used in localAlpha_eq_coreAlpha, selDeg ↔ cnt S (nbrs ·) through Fin 9 ↔ List.range 9,
-- then Finset.sum over Fin 9 ↔ List.sum over range 9.
theorem shareSeq_eq_coreShare … : shareSeq M p k = LocalWindow.coreShare M p k
```

### 2.3 Do the existing `Axioms` expose enough?

Yes for the model: `Axioms` is about the whole function `S : Nat → Bool`, and the share
is a function of `S` alone, so `AxiomsS` only adds the cap.  What the CNF has today
(`wincert.py:74-123`): one primary variable per ball vertex (radius 4: all vertices
within distance 4 of a centre), an endpoint flag per interior ball vertex, Sinz registers
for the endpoint budget and the alpha bounds.  The share needs, per share centre and
per non-path neighbour `q` (7 per centre): the 28 empty-square indicators, the two
counters and the threshold variables of `e1lib.py:77-96`.  All vertices they mention
are at distance ≤ 3 from the centre, inside the radius-4 ball (`e1lib.py:72,75`
asserts this).  The CNF does not need to state that `q` is unselected: `deg2` clauses
at the centre with both path neighbours forced (`window` units) already imply it, and
the Lean soundness never needs it (§4.2).

## 3. Lean: the automaton

### 3.1 Why the symbol stays `sym α` and the share becomes an edge weight

The task statement suggests `symbol = (α class, share class)`.  With `k = 5` the shard
check enumerates `6^5 = 7776` symbol combinations per (7-shape, next label)
(`check5R4`, `WindowAutomaton5R4Data.lean:136-141`; one shard ≈ one kernel-minute,
`README.md` of milestone 10).  With `S+1` share classes it enumerates `(6(S+1))^5`:
`S = 1` already costs 32× (≈ 20 h of kernel time over 34 shards) and `S = 2` 243×.  The
states grow the same way (`44064 → 44064·(S+1)^4`).  And a per-centre share class
carries little: single-centre shares are at most `4/15` α-units (`s0_radius4/README.md`),
while the useful information is the *sum over a five-centre window* (0.9 per vertex).

The sum is naturally an edge quantity.  Each automaton edge `e` appends one direction
and one count and is tested against the 5-centre window ending at the new vertex
(`Automaton.windows`, `refine.py:131-136`; `hw5` in `total_bound5R4`).  Give the edge the
weight

    W(e) = 10 M · sym(s_e) + T5(e),   T5(e) = certified lower bound on shareSum of that window

(units of `g = 2Mα + shareN` summed over 5 vertices: 5·2M·α for the new count, and the
window's share sum once).  Soundness of the telescoped sum: `Σ_e T5(e) ≤ Σ_e shareSum(W_e)
= Σ_j share_j · #{e : j ∈ W_e} ≤ 5 Σ_j share_j`, and `Σ_e 10 M sym s_e ≤ 10 M Σ_j α_j`.
This is exactly what `refine_share.py:72-75` computed (`s + T5/(5·2M)` per edge).
Lower bounds from shorter windows (pairs, triples, singles) can be folded into the same
table entry later (`max(T5, T4 + T1, …)`), but version 1 uses 5-centre windows only.

### 3.2 Generated data (`gen_lean_automaton5.py --tag R4S --share …`)

`WindowAutomaton5R4SData.lean` keeps `shapeIdx7`, `wshapeIdx5`, `forbMaskOf5`,
`potMaskOf5`, `cntIdx5`, `pot5`, `wforb5a`, `wforb5` (templates at
`gen_lean_automaton5.py:167-190`) and adds:

```lean
/-- Share lower bound of each window shape: `B`-bit fields at `symIdx syms 0`; `0` when
no certificate exists. -/
def shareMaskOf5R4S (s : Nat) : Nat := if s = 0 then … else … 0

def shareA5R4S (ds syms : List Nat) : Nat :=
  (shareMaskOf5R4S (wshapeIdx5R4S (shapeCode (canon ds))) >>> (B * symIdx syms 0)) &&& (2^B - 1)

/-- Both orientations are the same window (the sum is symmetric). -/
def shareT5R4S (ds syms : List Nat) : Nat :=
  max (shareA5R4S ds syms) (shareA5R4S ds.reverse syms.reverse)

def check5R4S (c : List Nat) : Bool :=
  !inducedPattern c ||
  allSym (fun t1 => allSym (fun t2 => allSym (fun t3 => allSym (fun t4 => allSym (fun s =>
    wforb5R4S (c.drop 5) [t4, s] || wforb5R4S (c.drop 4) [t3, t4, s] ||
    wforb5R4S (c.drop 3) [t2, t3, t4, s] || wforb5R4S (c.drop 2) [t1, t2, t3, t4, s] ||
    decide (P + pot5R4S (c.drop 1) [t2, t3, t4, s] ≤
      Q * (10 * M * s + shareT5R4S (c.drop 2) [t1, t2, t3, t4, s]) + pot5R4S (c.take 7) [t1, t2, t3, t4]))))))
```

Sizes: `symIdx` of 5 symbols is below `7^5 = 16807`, so with `B = 10` (bounds up to
1023; the measured optima are 120-292 at `M = 12`) a share mask is at most 168 kbit per
6-direction shape, the same order as the per-shape potential masks (1296 states × 6
bits today, × 14-16 bits with the share).  The kernel caches each shifted literal per
key, as for `forbMaskOf5R4` (`gen_lean_automaton5.py:76-78`).  One extra lookup per
symbol combination (two shifts for the two orientations): expect the shard check to
cost 1.3-2× the current minute.

Potential width.  The potentials come from `exact_check` (`refine.py:229-240`) on
weights `Q·W − P`; `W` is about 120× larger than today, so the range grows from 48
(`refine_L7_k5_K5_r4.json`, `potential_range: 44`) to roughly 5000-20000: `--pot-bits 14`
or `16`.  The final constant is `C = (2^bits − 1) + 7P − 60 M Q` (generalising
`gen_lean_chain5.py:13-14`, `prune_costly.lean_bound` `:20-22`), and the edges it costs
are `(2^bits − 1)/(P + 350 M Q)`: with `Q = 11` and 14 bits about 0.3 edges, with 16
bits about 1.3 edges.  Two remedies if that bites: prove the tight bound
`pot5R4S h t ≤ R` (`R` = actual range) by a kernel enumeration of the 34·1296 fields
instead of `Nat.and_lt_two_pow` (`pot5R4_le`, `WindowAutomaton5R4Data.lean:145`), or
divide all weights by their gcd.

The Python mirror (`gen_lean_automaton5.py:99-119`) must re-check the new inequality on
every shard transition, reading `T5` from the certified share index, and the
membership lemma stays as is.

### 3.3 Sequence lemmas (`gen_lean_chain5.py --share`, module `WindowAutomaton5R4SSequence.lean`)

```lean
def sumSh (sh : Nat → Nat) : Nat → Nat        -- Σ_{j=1}^{n} sh j, same shape as sumA (WindowAutomatonSequence.lean:45)
  | 0 => 0 | n + 1 => sumSh sh n + sh (n+1)

/-- Weighted window sum `Σ_{t<n} (10 M sym (a (t+7)) + shareT5 (dirs t+2 … t+7) (syms t+3 … t+7))`. -/
def S5S (M : Nat) (d a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => S5S M d a n + (10 * M * sym (a (n+7)) +
      shareT5R4S [d (n+2), d (n+3), d (n+4), d (n+5), d (n+6), d (n+7)]
        [sym (a (n+3)), sym (a (n+4)), sym (a (n+5)), sym (a (n+6)), sym (a (n+7))])

theorem step5R4S_raw … :      -- as step5R4_raw (:28-47) with the new right-hand side
    P + pot5R4S (x.drop 1) [sym t2, sym t3, sym t4, sym s] ≤
      Q * (10 * M * sym s + shareT5R4S (x.drop 2) [sym t1, sym t2, sym t3, sym t4, sym s]) +
        pot5R4S (x.take 7) [sym t1, sym t2, sym t3, sym t4]
-- needs shareT5R4S_canon_drop, like wforb5R4_canon_drop (:12-15), from canon_canon_drop /
-- canon_canon_drop_reverse (WindowAutomatonLemmas.lean:222,230)

theorem invariant5R4S … : ∀ n, n + 7 ≤ m → P * n + ΨR4S d a n ≤ Q * S5S M d a n + ΨR4S d a 0
-- as invariant5R4 (:69-88)

/-- The share premise: every five-centre window's table value is below the actual sum. -/
-- hs5 : ∀ j, j + 6 ≤ m → shareT5R4S [d j, …, d (j+5)] [sym (a (j+1)), …, sym (a (j+5))]
--          ≤ sh (j+1) + sh (j+2) + sh (j+3) + sh (j+4) + sh (j+5)

theorem S5S_le (M) (d a sh) (m) (hpos) (hs5) : ∀ n, n + 7 ≤ m →
    60 * M + S5S M d a n ≤ 10 * M * sumA a (n + 6) + 5 * sumSh sh (n + 6)
-- as sumA_ge5 (WindowAutomaton5Sequence.lean:101-119) for the α part (sym_le, six leading
-- counts ≥ 1), plus: Σ_{t<n} Σ_{i=3}^{7} sh (t+i) ≤ 5 · sumSh sh (n+6), proved per i
-- (Σ_{t<n} sh (t+i) ≤ sumSh sh (n+6) because {i, …, n+i-1} ⊆ {1, …, n+6} for 3 ≤ i ≤ 7).

theorem total_bound5R4S (M) (d a sh) (m) (hm : 7 ≤ m) (hpos) (hind) (hw2 hw3 hw4 hw5) (hs5) :
    P * m ≤ Q * (10 * M * sumA a (m - 1) + 5 * sumSh sh (m - 1)) + C
-- C = (2^bits - 1) + 7 P - 60 M Q, as total_bound5R4 (:91-107)
```

### 3.4 Conditional and unconditional theorems

`AggregateDirectionNConditional.lean` (mathlib), generated like
`AggregateDirection236Conditional.lean:15-39`:

```lean
theorem upper_N_of_direction_windows5R4S {m : Nat} (p : Snake m)
    (hw2 hw3 hw4 hw5 : …as today with wforb5R4S…)
    (hs5 : ∀ j, j + 6 ≤ m → shareT5R4S [pathDir p j, …, pathDir p (j+5)]
      [sym (countSeq p (j+1)), …, sym (countSeq p (j+5))] ≤
      shareSeq 12 p (j+1) + shareSeq 12 p (j+2) + shareSeq 12 p (j+3) + shareSeq 12 p (j+4) + shareSeq 12 p (j+5)) :
    m ≤ N
-- countSeq_facts for the endpoint and positivity facts, charge_facts (§1) in place of the
-- incidence line, total_bound5R4S with a := countSeq p, sh := shareSeq 12 p, sumA_eq_psum
-- (AggregateDirectionConditional.lean:9) and its sumSh twin; then omega:
-- (P + 4200 Q) m ≤ 1100520 Q + C.
```

Bridge (`DirectionWindowBridge5R4S.lean`, core, generated; copies
`DirectionWindowBridge5R4.lean`):

```lean
def shareBit5 (c syms : List Nat) : Nat := shareA5R4S-lookup on the canonical shape c   -- as forbBit5 (:36)

/-- Every nonzero table entry `T` has a certificate with cap `T - 1`. -/
def coverShareOK5 (c : List Nat) : Bool :=
  allSyms0 5 (fun syms => shareBit5 c syms == 0 || decide ((c, syms, shareBit5 c syms - 1) ∈ shareKeysR4S))
theorem cover_share5_6 : allRGS 6 0 coverShareOK5 = true := by decide +kernel   -- as cover_table5_6 (:64)

theorem window_share5 (h : AllShareRefuted) (r : Nat) (hr : r + 6 ≤ m) :
    shareA5R4S (dsOf p r 6) (symsOf p r 6) ≤ coreShare 12 p (r+1) + … + coreShare 12 p (r+5)
-- T = 0 trivial; else cover gives the key, AllShareRefutedList.mem gives
-- RefutedShare (winOf c) (boundsOf syms) 12 (T-1), refuted_share_dir gives T ≤ Σ coreShare
-- (as window_refute5 :97-133 with seenAfter, canon_eq_map, getD_symsOf).

theorem share_window5 (h) (r) (hr) : shareT5R4S (dsOf p r 6) (symsOf p r 6) ≤ Σ_{i=1}^{5} coreShare 12 p (r+i)
-- max of both orientations: the reversed one via revSnake, dsOf_rev / symsOf_rev
-- (DirectionWindowBridge.lean, as in no_forb_window5 :136-145) and coreShare_rev; the
-- reversed window's centres are the same five vertices, so the sum is the same.

theorem direction_share_core5 (h : AllShareRefuted) (p : Snake m) :
    ∀ j, j + 6 ≤ m → shareT5R4S [pathDir p j, …] [symC (coreAlpha p (j+1)), …] ≤ Σ coreShare …
-- pathDir_eq_dir, as direction_windows_core5 (:151-180)
```

`AggregateDirectionNUnconditional.lean` rewrites `countSeq` to `coreAlpha`
(`countSeq_eq_coreAlpha`, `AggregateDirectionUnconditional.lean:21`) and `shareSeq` to
`coreShare` (`shareSeq_eq_coreShare`), and takes both `AllRefuted236`-style premises:
the exclusion premise (`direction_windows_core5` of the existing or a re-pruned
exclusion set) and `AllShareRefuted`.  `UpperBoundN.lean` discharges both from
`LocalWindowDirUnsatR4S` (exclusions) and `LocalWindowShareUnsatR4S` (shares).

### 3.5 The cap `K` and the lumped symbol `6+`

Unchanged in version 1: symbols `1..6`, `cntIdx5` base 6, `symIdx` base 7, states
`34 × 6^4 = 44064`.  A share certificate for symbol `6` must hold for `α ∈ 6..21`
(`boundOf 6 = (6, 21)`), which is why `s0_radius4/README.md` notes that the lumped
`6+` hides `α = 7-11` and costs share.  Raising the cap to `K = 8` (symbols `1..9`,
`allSym` over 9) multiplies the per-shard enumeration by `(9/6)^5 ≈ 7.6` and the
states by `(9/6)^4 ≈ 5`; `gen_lean_automaton5.py` hard-codes 6 in `cntIdx5`, `allSym`
(`WindowAutomatonDefs.lean:96`) and `sym` (`:49`, `symC` in
`LocalWindowDirBridge.lean:49`, `boundOf`), so this is a separate parametrisation task
(already noted for the `K = 8` radius-4 run in milestone 10's README).  It is the
natural stage after the share lands (§5, stage 6).

## 4. Solver side: encoding, tags and soundness

### 4.1 The CNF (`milestones/10-window-aggregate/scripts/wincert.py` + a share module)

Promote `e1lib.ShareModel` (`milestones/11-local-ceiling/s0_radius4/e1lib.py:50-96`) to
`wincert_share.py` with a `ShareEncoding(window, alpha, radius, M, cap)` built on
`wincert.Encoding` (`wincert.py:56-123`, unchanged), recording a `kind` per clause as
`Encoding.add` does.  Variable order, after the base encoding's variables:

1. for each centre `c = window[i]` (i = 1..k) and each `kk ∉ {d₁, d₂}` (7 values), with `q = c ^ 2^kk`:
   * 28 indicators `E[q,ab]` for `ab ∈ freePairs kk kk` (order of `itertools.combinations` = order of `freePairs`), clause `[X q, X (q^a), X (q^b), X (q^ab), E]` (`e1lib.py:80`);
   * totalizer `eTot_q` over the 28 `E`s (`unary_ge … up=True`, `e1lib.py:22-43`), `tot_up` clauses;
   * totalizer `dTot_q` over the 9 primaries `X (q ^ 2^t)` in the order of `nbrs q` (`unary_ge … down=True`), `tot_down` clauses;
   * `u[q,t]` for `t = 1..tmax_q`, `tmax_q = min(cap + 1, 28 M)`, with for every `dd = 1..9` such that `cneed = ⌈t·dd/M⌉ ≤ 28` the clause `[u] ++ (if cneed ≥ 1 then [-eTot_q[cneed]]) ++ (if dd ≤ 8 then [dTot_q[dd+1]])` (`e1lib.py:85-96`);
2. a cap totalizer `capTot` over all `u` literals in that order (`unary_ge … up=True`) and the unit clause `[-capTot[cap+1]]`.

In `e1lib` the cap is a pysat `ITotalizer` under assumptions, which is right for the
binary search (`minimise`, `minimise2`) but not for a committed CNF: the certificate
must be a cold solve of the static clause set so that `gen_lean_sat.py` can rebuild it
clause for clause (`process`, `gen_lean_sat.py:252-283` asserts `ref.clauses ==
enc.clauses`).  So: search with `e1lib`, then re-encode with the static cap and certify
with `wincert.decide` + `certify_unsat` (`wincert.py:151-195`; cycle cuts are added
lazily and tagged `cut` as today).  Leaf totalizer outputs are the input literals
themselves (`rec([l]) = [None, l]`, `e1lib.py:25`); the tag checker must accept that
(§4.2).

A new `certify_share.py` (from `certify_direction.py`) writes
`certificates/share_r4/S<ds>A<syms>K<K>.cnf.gz` and the index
`data/share_certificates_r4.json` with per case `{dirs, alpha, M, cap, radius,
cnf_sha256, drup_sha256, drat_trim_verified, seconds}`.  `gen_lean_core.py --set share`
extracts cores (CaDiCaL portfolio, `README.md` "Shorter proofs") into
`LocalWindowCnf/S<ds>A<syms>K<K>.lean` (`window`, `bounds`, `cap`, `raw`) and writes
`LocalWindowShareKeysR4S.lean`:

```lean
def shareKeysR4S : List (List Nat × List Nat × Nat) := [ ([0, 1, 2, 3, 0, 4], [2, 6, 2, 4, 6], 107), … ]
def AllShareRefutedList : List (List Nat × List Nat × Nat) → Prop
  | [] => True
  | k :: ks => RefutedShare (winOf k.1) (boundsOf k.2.1) 12 k.2.2 ∧ AllShareRefutedList ks
def AllShareRefuted : Prop := AllShareRefutedList shareKeysR4S
```

(`winOf`, `boundsOf`: `LocalWindowDirModel.lean:24,29`; `AllRefutedList` `:32-42` is the model.)

### 4.2 Clause soundness (`work/final_lean/LocalWindowTags.lean`)

Keep the existing `MT` `:35`, `Kind` `:50`, `Ctr` `:56`, `Tag` `:65`, `tau` `:107`,
`checkAll` `:286`, `sound` `:749`, `refuted_of_sat` `:761` untouched, so that the 732
existing `LocalWindowSat` modules still build.  Add, in the same namespace:

**Meanings.** Three new `MT` leaves (the tree type is reused; old modules never
produce them):

| leaf | variable | value under `tauS` |
|---|---|---|
| `.sq q a b` | `E[q,(a,b)]` | `emptyPred S q (a, b)` |
| `.t i lo hi c` | output `c` (1-based) of totalizer `i` on the literal block `lits[lo:hi]` | `decide (c ≤ blockCount i lo hi)`, `blockCount i lo hi = (((tots.getD i dfltTot).lits.drop lo).take (hi - lo)).countP (lv (baseS …))` |
| `.u q t` | `u[q,t]` | `decide (t ≤ M * emptyCount S q / cnt S (nbrs q))` |

`baseS S E M Mres` extends `base` `:97` with `.sq` and `.u`; `tauS` extends `tau`
with `.t` (counts over base-valued literals only, so no circularity; the checker
requires every totalizer literal to be `.p`, `.e`, `.sq` or `.u`).  New data:
`structure Tot where lits : List Nat` (literal codes) and, per share neighbour,
`structure ShareQ where c : Nat; kk : Nat; q : Nat; eT : Nat; dT : Nat; tmax : Nat`.
`checkAllS M cs tots qs w b Mres cap tags raw` checks the old `ctrOK` for `cs`, a
`shareOK` for the share data, and `ckAllS` over the tags.

**`shareOK`** (one kernel check, like `ctrOK` `:201-213`): `qs` equals
`centres.flatMap (fun c => ((List.range 9).filter (fun k => k ≠ c.d₁ ∧ k ≠ c.d₂)).map (…))`
with `q = c.v ^^^ (1 <<< kk)`; for each entry `tots[eT].lits = (freePairs kk kk).map (fun ab => posCode (.sq q ab.1 ab.2))` (checked by meaning, not by variable number), `tots[dT].lits.map vl = nbrs q` with all literals positive `.p`; `tots[capT].lits` walked against `qs.flatMap (fun s => (List.range s.tmax).map (fun t => (s.q, t+1)))`, each literal a positive `.u q t` with the expected `(q, t)`.

**Tags and their soundness lemmas** (each is a `sound_*` like `sound_window` … `sound_over` `:550-712`, proved by `clause_intro` and the semantic values):

| tag | clause shape | checker verifies | soundness argument |
|---|---|---|---|
| `emptyE` | `[X q, X q^a, X q^b, X q^ab, E]` | 4 positive `.p` whose vertices are the corners of the `.sq q a b` leaf of the 5th (positive) literal | if all four corners are unselected then `emptyPred` is true; else one `X` literal is true |
| `totUp i` | `[o] ++ opt [-a] ++ opt [-b]` | `o = .t i lo hi (ia+ib)`, `a = .t i lo mid ia` (absent ⇒ `ia = 0`), `b = .t i mid hi ib` (absent ⇒ `ib = 0`), `lo ≤ mid ≤ hi ≤ length`; a leaf node `[lo, lo+1)` with `c = 1` may be the input literal `lits[lo]` itself | `blockCount lo hi = blockCount lo mid + blockCount mid hi` (`List.countP_append` on `drop`/`take`); `a ≥ ia ∧ b ≥ ib → o ≥ ia+ib` |
| `totDown i` | `[-o] ++ opt [a] ++ opt [b]` | `o = .t i lo hi (ia+ib+1)`, `a = .t i lo mid (ia+1)` (absent ⇒ `ia = mid - lo`), `b = .t i mid hi (ib+1)` (absent ⇒ `ib = hi - mid`) | `o ≥ ia+ib+1 → a ≥ ia+1 ∨ b ≥ ib+1` (a block count never exceeds its length: `List.countP_le_length`) |
| `shareCl q t dd` | `[u] ++ opt [-ge] ++ opt [gd]` | `u = .u q t`, `q` listed in `qs` with totalizers `eT`, `dT`; `ge = .t eT 0 28 cneed` with `cneed = (t*dd + M - 1) / M` (absent ⇒ `cneed = 0`); `gd = .t dT 0 9 (dd+1)` (absent ⇒ `dd = 9`); `1 ≤ t`, `1 ≤ dd ≤ 9` | suppose `u` false, `ge` true, `gd` false: `d := cnt S (nbrs q) ≤ dd`, `e28 ≥ cneed` so `M·e28 ≥ t·dd` (`a ≤ M * ((a + M - 1) / M)` for `M ≥ 1`), `e28 ≤ emptyCount S q` (`(freePairs kk kk).Sublist (freePairs 9 9)`, nine cases by `decide`, then `List.Sublist.countP_le`), and `d ≥ 1` because `c = q ^^^ 2^kk ∈ nbrs q` is a window vertex (`Axioms.window_sel`); then `t > M e0 / d` gives `t·d > M·e0 ≥ M·e28 ≥ t·dd ≥ t·d` (`Nat.div_lt_iff_lt_mul`), contradiction |
| `shareCap` | `[-o]` | `o = .t capT 0 n (cap+1)` with `capT` the cap totalizer of `shareOK` | `countP = Σ_{s ∈ qs} #{t ∈ 1..tmax : t ≤ fl(q)} ≤ Σ_{s ∈ qs} fl(q) ≤ shareSum M S centres ≤ cap` (`AxiomsS.share_le`); the first inequality is `List.countP` over `range tmax` of `t+1 ≤ x`, at most `x`; the second drops the two path directions of each centre from `shareLocal`'s nine-term sum (terms are `≥ 0`) |

`window`, `deg2`, `degPos`, `endSel`, `lowEnd`, `endLow`, `cut`, `first`, `zero`,
`mono`, `step`, `over` keep their lemmas; `ctr_bound` `:499` keeps its three kinds
(the Sinz counters for `ends`, `hi`, `lo` are unchanged in the share CNF).  Then

```lean
theorem soundS (M : MT) (cs : List Ctr) (tots : List Tot) (qs : List ShareQ) (w) (b) (Mres cap : Nat)
    (tags) (raw) (h : checkAllS M cs tots qs w b Mres cap tags raw = true) (S E : Nat → Bool)
    (ax : AxiomsS S E w (centresOf w b) Mres cap) :
    cnfTrue (tauS S E M Mres cs tots) (raw.map (·.map decodeLit)) = true

theorem refutedShare_of_sat {window bounds M cap f}
    (hsat : ∀ S E, AxiomsS S E window (centresOf window bounds) M cap → ∃ τ, cnfTrue τ f = true)
    (hunsat : Unsat f) : RefutedShare window bounds M cap
```

**Packed data** (`LocalWindowTagsPacked.lean`): `tagOf` `:47` reads a 4-bit kind
(`Nat.land x 15`); the share set has 17 kinds, so a new decoder `tagOfS` uses 5 bits
(layout 5 + 8 + 16 + 16 = 45 ≤ 48; `shareCl` packs `dd` in the 8-bit field, `q` and
`t` in the 16-bit fields; `totUp`/`totDown` the totalizer id in the 8-bit field).
`leafOf` `:30` uses a 2-bit type; `.t i lo hi c` needs `3 + 8 + 12 + 12 + 12 = 47` bits
for blocks up to 4096 literals, which is tight: use a 64-bit leaf stream for the share
modules (`mtB64`, same recursion as `mtB` `:38` with the mask `2^64 - 1` and shift 64).
`gen_lean_sat.py` gets the mirror classes (`TaggedShareEncoding`, `TAG_KINDS_S`,
`packed_tree64`, `packed_tags5`), a new entry of `DIR_SETS` (`:348-356`) named `share`
with premise `AllShareRefuted` and modules `LocalWindowShareSatR4S` /
`LocalWindowShareUnsatR4S` (templates `write_dir_aggregate` `:371`, `write_dir_unsat`
`:409`), and emits `satS`/`checkS` in `write_module` `:286-340`.

**Replays.** A radius-4 five-centre share CNF has about 440 primaries plus roughly
980 indicators, 5000 totalizer outputs, 3800 thresholds (`tmax ≈ 110` at `cap ≈ 108`)
and 7000 cap-totalizer outputs: 15-20k variables, far beyond the offset 4000 of
`LratFastO4k*` (`gen_checker_variants.py` header).  New variants `LratFast2_O24k_{18,19,20}`
(offset 24000, words wide enough for `2·24000 < 2^W` and core clause keys below
`2^(W-1)`) are a constant substitution in `gen_checker_variants.py`, but they must be
built once and timed; wider words make every hint word longer and the kernel slower.
Lowering `tmax` (e.g. to `cap/5 + 20` per `q`, which weakens nothing when the window's
share is spread over 35 neighbours but may lose a proof) halves the variable count.

### 4.3 The refinement loop (`refine.py --share`, or a production `refine_share.py`)

* Oracle entries keyed by `(key5, K)` with status `UNSAT` / `SAT(witness)` /
  `TIMEOUT`; `Oracle.query` unchanged for plain exclusions.
* `Automaton.edges` returns integer weights `W(e) = 10 M sym + T5(key5(e))` where
  `T5 = max {K+1 : (key5, K) UNSAT}` (0 if none), and a fixed `M = 12`.
* Howard on `W`; `exact_check` with `(P, Q)` of the cycle mean in `W` units.
* For each 5-window of the minimum cycle without a bound: a threshold schedule
  (`threshold.py` logic, `s0_radius4/threshold.py`): try `K = 107` (`T = 108`, 0.9 per
  vertex), then `149`, `199`, with a per-call limit; a `SAT` witness below `108` records
  the witness value as an upper bound so the window is not retried above it; `TIMEOUT`
  leaves `T5 = 0`.  `estimate.py` showed 4.76-4.77 if the untested windows force 108
  (not rigorous); the loop converges when every window of the minimum cycle is tested.
* The 166 windows already tested (`threshold_results.jsonl`, `ceiling_results.jsonl`,
  `refshare_results.jsonl`: 114 UNSAT at 108, 25 at 150, 13 timeouts, 14 SAT with
  witnesses 88-148) seed the oracle but need fresh DRAT runs with the static cap.
* `direction_bound.py` (`bound`, `:39-62`) gets the weighted recomputation
  `(2M·T_int + Sh_int) ≤ M (18342 − 70 m)` for the independent check of the automaton.
* `prune_costly.py` (`lean_bound`, `:20-22`) gets `lean_bound(P, Q, bits, M) =
  (91710 M Q + C) // (P + 350 M Q)` and can drop expensive share certificates (lower
  `K` is a weaker claim and a shorter proof; a dropped certificate sets `T5 = 0`, it
  does not invalidate the automaton).

## 5. Staged plan, estimates, risks, reuse

Effort is engineering time; kernel time is separate.  Stage 2 is the largest Lean
item; stage 4 dominates machine time.

| stage | content | gives | effort |
|---|---|---|---|
| 0 | `ShareCharge.lean`: `emptyAt`, `selDeg`, `shareN`, `share_total_le`, `charge_total_le`, `charge_facts` (§1) | the weighted identity as a mathlib theorem; no bound change | 1-2 days |
| 1 | `AxiomsS`, `RefutedShare`, `shareLocal`, frame invariance, `refuted_share_bridge`, `refuted_share_dir`, `coreShare_rev`, `shareN_eq_coreShare` (§2) | the statement every share certificate proves, connected to `shareN` | 3-5 days |
| 2 | `wincert_share.py`, `TaggedShareEncoding`, `Tags` extension (`checkAllS`, `soundS`, five lemmas), packed decoders, `gen_lean_sat.py --set share`; exit test: one window from `windows_results.jsonl` (e.g. `dirs 0,1,2`, `α (2,2)`, proved `shareN = 10`, `M = 12`) certified end to end with `RefutedShare … 12 9`, kernel-checked `checkS` and a replay | the pipeline works on one certificate; still no bound change | 5-8 days, plus new `LratFast2_O24k*` variants built and timed |
| 3 | production share loop (§4.3) on the radius-4 L7 k5 K5 automaton, run to convergence | the solver-side bound (expected 231-233; 230 "only barely", `s0_radius4/README.md`) | 2-3 days coding; 2-5 CPU-days at nice 19 (the original loop took about 170 rounds; threshold tests 3-160 s each, 13/166 timed out) |
| 4 | DRAT certification of every `(key, K)` on the final automaton, cores (`gen_lean_core.py --set share`, portfolio), Sat modules, replays (`run_direction_replays.py --set share`) | the premise `AllShareRefuted` as a Lean theorem | 1-2 days coding; kernel time unknown: the 237 set (387 windows, 289 M hints) took 34 kernel-hours, so 1-10 M hints per share window × 500-2000 windows is 100-1000 kernel-hours; prune aggressively (stage 3 should already minimise the certificate set) |
| 5 | `gen_lean_automaton5.py --share --tag R4S --pot-bits 14`, `gen_lean_chain5.py --share` (sequence, conditional, bridge, unconditional, `UpperBoundN`), `chain_audit.py` | **the first Lean-checked bound with the share**, 231-233 | 2-3 days; shards ≈ 1-2 kernel-hours, cover and audit minutes |
| 6 (later) | cap `K = 8`, sub-window bounds folded into `T5`, `M = 2520` for exact shares | 230 and below, against the 227-224 ceiling of the 208/224 adversaries | separate design |

**What gives a bound at each point.** Nothing before stage 5 changes the proved bound:
single-centre lower bounds (proved: `4/15`, `3/20`, `≥ 1/24`, `0` for α = 1, 2, 3, 5)
move the mean to 3.933 (236.66); pairs and triples (`spec_pair_lo.json`,
`automaton3.py`) to 3.87-4.0; the share-aware refinement after 8 rounds stood at 3.93.
So there is no cheap intermediate Lean milestone with a smaller bound: stage 2's exit
test is the intermediate milestone (one share certificate through the kernel), and
the first improvement needs the converged five-centre set.

**Risks.**

1. *Replay size.* Share CNFs are 3-4× larger in variables and have long totalizer
   chains; LRAT sizes for threshold refutations are unmeasured.  Mitigation: measure
   on ten windows in stage 2 before committing to stage 3's threshold schedule; prefer
   the smallest `K` that still gives the target; checker variants with offset 24000.
2. *Potential range.* 14-16-bit fields; the loss `(2^bits − 1)/(P + 350 M Q)` is
   0.3-1.3 edges unless the tight range is proved (§3.2).  The generator already
   asserts `pi.max() ≤ MAXP` (`gen_lean_automaton5.py:71`).
3. *The lumped symbol.* Certificates for symbol 6 cover `α ∈ 6..21` and prove less
   share; the E1 note expects a larger cap to be needed for 230.  Not in version 1.
4. *Timeouts.* Each untested or timed-out window contributes `T5 = 0`; 8% timed out at
   60-160 s in E1.  The loop must converge with those at 0 or spend more time per window.
5. *Exclusion set drift.* The 732 exclusions were pruned for the unweighted mean
   (`direction_certificates_r4c.json`); the weighted minimum cycle may run through
   windows that were dropped as too costly, so the share loop may also need a few new
   plain exclusions (plain radius-4 certificates, existing pipeline).
6. *Kernel cost of the shard check* with the extra lookup and wider fields: 1.3-2×
   (34 shards at 1-2 minutes each; fine).
7. *Format changes* (`Tag` kinds > 16, 64-bit leaves) must not touch the decoders the
   732 existing modules use: keep `tagOf`/`mtB`/`checkAll`/`sound` as they are and add
   `tagOfS`/`mtB64`/`checkAllS`/`soundS`.

**Reused unchanged.** `SquareIncidence.lean` (all of it), `Axioms`, `Refuted`, the 732
exclusion certificates with their `LocalWindowCnf`/`LocalWindowSat`/`LocalWindowUnsat`
modules and `AllRefuted236`, `forbMaskOf5R4`, `DirectionWindowBridge5R4` (cover and
`direction_windows_core5`), `WindowAutomatonDefs`/`Lemmas`/`Bridge` (`canon`,
`inducedPattern`, `pathDir`), the Sinz counter families and `ctr_bound`, `wincert.py`
and `decide`/`certify_unsat`, `gen_lean_core.py`'s core extraction and `core_lrat`,
`run_direction_replays.py` and `guarded_lake_build.py`, `LratFast2`/`LratFast2F`
(with new offset variants), `refine.py`'s `Automaton`, `howard`, `exact_check`,
`prune`, and `countSeq_facts`'s endpoint and positivity facts.
