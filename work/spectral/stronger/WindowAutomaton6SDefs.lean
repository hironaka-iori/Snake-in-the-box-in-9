/-
Share-weighted six-centre (k = 6) direction automaton: definitions and the sequence bound.

Core Lean only.  The automaton of `WindowAutomaton6Defs` (state: canonical 7-direction shape
`d(n..n+6)` and the five lumped counts `a(n+2..n+6)`; step: one more direction `d(n+7)` and
count `s = a(n+7)`) with two additions (milestones/28-combined-identities, milestones/31-233-cost,
"Lean plan"; milestones/33-233-lean):

* **Share weight.** The step weight is `120 * s + S5`, where `S5 = share6 T (c.drop 2) [t1..t4, s]`
  is a certified lower bound on the M = 12 corner-share sum of the trailing 5-window
  (directions `d(n+2..n+7)`, centres `n+3..n+7`), read from the share table of `T`: a field of
  `sbits` bits per (6-direction shape, first count, the other four counts), looked up in both
  orientations; `share6` is the larger value.  The share table is backed by certificates in
  `DirectionWindowBridge6S` (`ShareCover`).
* **H8 cuts.** The 8-direction step window `c` with the six counts `a(n+2..n+7)` (the first
  interior vertex `n+1` uncounted), stored reversed as in the H9 table of `WindowAutomaton7Defs`:
  key `(canon (rev c), rev counts)`, certificate `Refuted (winOf ds) (boundsOf syms)` with 6
  bounds for 7 interior vertices.  Sparse, so it is a search tree `htree` (`wforbH8`).

`check6SAt T c t0`: for every transition, a k6 window of 3..7 directions ending at the new
vertex is excluded (either orientation), or the H8 window is, or
`num + pot(next) ≤ den * (120 s + share6) + pot(current)`.

`total_bound6S`: `num * (m - 7) ≤ den * Σ_{n < m-7} (120 sym a(n+7) + S5 n) + (2^bits - 1)`,
in the `Combined.rsum` form of `CombinedShareToy.combined_bound` (milestone 28), which then gives
`(num + 4200 den) m ≤ 1099800 den + 7 num + (2^bits - 1)` (`AggregateDirection6SConditional`).
-/
import WindowAutomaton7Defs
import CombinedShareToy

namespace Snake9.WindowAutomaton

/-- Tables of a share-weighted six-centre automaton.  `k6` carries the exclusion rows, the
potential rows and `lambda = num / den` exactly as for `Tables6`. -/
structure Tables6S where
  k6 : Tables6
  /-- H8 keys: `encB 9 (ds ++ syms) 0` of each key (8 directions, 6 counts) -/
  htree : NTree
  /-- 6-direction (5-centre) shape code ↦ share row -/
  sIdx : Nat → Nat
  /-- share row, first count ↦ `sbits`-wide fields at `cntIdx6` of the other four counts -/
  shr : Nat → Nat → Nat
  sbits : Nat

/-- Share level of the 5-window with shape code `code` and counts `t` (one orientation). -/
def shareAt6 (T : Tables6S) (code : Nat) : List Nat → Nat
  | [] => 0
  | t0 :: rest => (T.shr (T.sIdx code) t0 >>> (T.sbits * cntIdx6 rest 0)) &&& (2 ^ T.sbits - 1)

def shareA6 (T : Tables6S) (ds t : List Nat) : Nat := shareAt6 T (shapeCode (canon ds)) t

/-- Share level of a 5-window: the larger of the two orientations. -/
def share6 (T : Tables6S) (ds t : List Nat) : Nat :=
  max (shareA6 T ds t) (shareA6 T ds.reverse t.reverse)

/-- H8 lookup of the step window `ds` (8 directions) with counts `syms` (6 counts, the first
interior vertex uncounted), in the reversed key form. -/
def wforbH8 (T : Tables6S) (ds syms : List Nat) : Bool :=
  T.htree.mem (encB 9 (canon ds.reverse ++ syms.reverse) 0)

/-- Step test of the eight-direction window `c` from the states with first count `t0`. -/
def check6SAt (T : Tables6S) (c : List Nat) (t0 : Nat) : Bool :=
  !inducedPattern c ||
  allSym (fun t1 => allSym (fun t2 => allSym (fun t3 => allSym (fun t4 => allSym (fun s =>
    wforb6 T.k6 (c.drop 5) [t4, s] || wforb6 T.k6 (c.drop 4) [t3, t4, s] ||
    wforb6 T.k6 (c.drop 3) [t2, t3, t4, s] || wforb6 T.k6 (c.drop 2) [t1, t2, t3, t4, s] ||
    wforb6 T.k6 (c.drop 1) [t0, t1, t2, t3, t4, s] ||
    wforbH8 T c [t0, t1, t2, t3, t4, s] ||
    decide (T.k6.num + pot6 T.k6 (c.drop 1) [t1, t2, t3, t4, s] ≤
      T.k6.den * (120 * s + share6 T (c.drop 2) [t1, t2, t3, t4, s]) +
        pot6 T.k6 (c.take 7) [t0, t1, t2, t3, t4]))))))

/-- The step test holds for every canonical eight-direction window and first count. -/
def StepOK6S (T : Tables6S) : Prop :=
  ∀ c : List Nat, c.length = 8 → isRGS c 0 = true → ∀ t0, 1 ≤ t0 → t0 ≤ 6 →
    check6SAt T c t0 = true

/-- What the 204 shards prove. -/
def ShardsOK6S (T : Tables6S) (shapes : List (List Nat)) : Prop :=
  ∀ h ∈ shapes, ∀ t0, 1 ≤ t0 → t0 ≤ 6 → allBelow 9 (fun d => check6SAt T (h ++ [d]) t0) = true

theorem check6S_of_shards (T : Tables6S) (shapes : List (List Nat)) (hr : ShapesCover shapes = true)
    (hs : ShardsOK6S T shapes) : StepOK6S T := by
  intro c hc hrgs t0 h1 h6
  have hm := allRGS_spec 8 0 _ hr c hc hrgs
  simp only [shapeTest6] at hm
  by_cases hind : inducedPattern c = true
  · rw [hind] at hm
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hm
    obtain ⟨hmem, hlt⟩ := hm
    have hsplit : c = c.take 7 ++ c.drop 7 := (List.take_append_drop 7 c).symm
    have hlen : (c.drop 7).length = 1 := by simp [hc]
    obtain ⟨d, hd7⟩ : ∃ d, c.drop 7 = [d] := by
      match h : c.drop 7, hlen with
      | [d], _ => exact ⟨d, rfl⟩
    have hd : d < 9 := by
      have := hlt d (by rw [hd7]; exact List.mem_singleton.mpr rfl)
      simpa using this
    rw [hsplit, hd7]
    exact allBelow_spec 9 _ (hs _ hmem t0 h1 h6) d hd
  · unfold check6SAt
    simp [hind]

/-- A table with zero potential and `num ≤ 120 den` passes every step test (toy instances). -/
theorem stepOK6S_of_trivial (T : Tables6S) (hp : ∀ r t, T.k6.pot r t = 0)
    (hnd : T.k6.num ≤ 120 * T.k6.den) : StepOK6S T := by
  intro c _ _ t0 _ _
  unfold check6SAt
  have hz : ∀ h t, pot6 T.k6 h t = 0 := by
    intro h t
    unfold pot6
    cases t with
    | nil => rfl
    | cons t0 rest => simp only [potAt6, hp, Nat.zero_shiftRight, Nat.zero_and]
  refine Bool.or_eq_true_iff.2 (Or.inr ?_)
  refine allSym_of_forall _ (fun t1 _ _ => allSym_of_forall _ (fun t2 _ _ =>
    allSym_of_forall _ (fun t3 _ _ => allSym_of_forall _ (fun t4 _ _ =>
    allSym_of_forall _ (fun s hs _ => ?_)))))
  simp only [hz, Nat.add_zero, Bool.or_eq_true, decide_eq_true_eq]
  right
  have h1 : 120 ≤ 120 * s + share6 T (c.drop 2) [t1, t2, t3, t4, s] := by omega
  have := Nat.mul_le_mul_left T.k6.den h1
  omega

/-! ### Transport: the step test applies to an arbitrary window -/

theorem shareA6_canon_drop (T : Tables6S) (ds t : List Nat) (n : Nat) :
    shareA6 T ((canon ds).drop n) t = shareA6 T (ds.drop n) t := by
  unfold shareA6
  rw [canon_canon_drop]

theorem share6_canon_drop (T : Tables6S) (ds t : List Nat) (n : Nat) :
    share6 T ((canon ds).drop n) t = share6 T (ds.drop n) t := by
  unfold share6 shareA6
  rw [canon_canon_drop, canon_canon_drop_reverse]

theorem wforbH8_canon (T : Tables6S) (ds syms : List Nat) :
    wforbH8 T (canon ds) syms = wforbH8 T ds syms := by
  unfold wforbH8
  rw [canon_canon_reverse]

/-- The step inequality for an arbitrary eight-direction window. -/
theorem step6S_raw (T : Tables6S) (hT : StepOK6S T) (x : List Nat) (hx : x.length = 8)
    (t0 t1 t2 t3 t4 s : Nat)
    (h0 : 1 ≤ t0) (h1 : 1 ≤ t1) (h2 : 1 ≤ t2) (h3 : 1 ≤ t3) (h4 : 1 ≤ t4) (hs : 1 ≤ s)
    (hind : inducedPattern x = true)
    (hw2 : wforb6 T.k6 (x.drop 5) [sym t4, sym s] = false)
    (hw3 : wforb6 T.k6 (x.drop 4) [sym t3, sym t4, sym s] = false)
    (hw4 : wforb6 T.k6 (x.drop 3) [sym t2, sym t3, sym t4, sym s] = false)
    (hw5 : wforb6 T.k6 (x.drop 2) [sym t1, sym t2, sym t3, sym t4, sym s] = false)
    (hw6 : wforb6 T.k6 (x.drop 1) [sym t0, sym t1, sym t2, sym t3, sym t4, sym s] = false)
    (hh8 : wforbH8 T x [sym t0, sym t1, sym t2, sym t3, sym t4, sym s] = false) :
    T.k6.num + pot6 T.k6 (x.drop 1) [sym t1, sym t2, sym t3, sym t4, sym s] ≤
      T.k6.den * (120 * sym s + share6 T (x.drop 2) [sym t1, sym t2, sym t3, sym t4, sym s]) +
        pot6 T.k6 (x.take 7) [sym t0, sym t1, sym t2, sym t3, sym t4] := by
  have hc := hT (canon x) (by rw [length_canon, hx]) (canon_isRGS x) (sym t0)
    (sym_ge_one _ h0) (sym_le_six _)
  unfold check6SAt at hc
  rw [inducedPattern_canon, hind] at hc
  simp only [Bool.not_true, Bool.false_or] at hc
  have h := allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ hc
    (sym t1) (sym_ge_one _ h1) (sym_le_six _)) (sym t2) (sym_ge_one _ h2) (sym_le_six _))
    (sym t3) (sym_ge_one _ h3) (sym_le_six _)) (sym t4) (sym_ge_one _ h4) (sym_le_six _))
    (sym s) (sym_ge_one _ hs) (sym_le_six _)
  rw [wforb6_canon_drop, wforb6_canon_drop, wforb6_canon_drop, wforb6_canon_drop,
    wforb6_canon_drop, hw2, hw3, hw4, hw5, hw6, wforbH8_canon, hh8, pot6_canon_drop,
    pot6_canon_take, share6_canon_drop] at h
  simpa using h

/-! ### Sequence consequence -/

/-- The step weight of step `n`: `120 sym a(n+7)` plus the share level of the 5-window
`d(n+2..n+7)` with the counts `a(n+3..n+7)`. -/
def w6S (T : Tables6S) (d a : Nat → Nat) (n : Nat) : Nat :=
  120 * sym (a (n+7)) + share6 T [d (n+2), d (n+3), d (n+4), d (n+5), d (n+6), d (n+7)]
    [sym (a (n+3)), sym (a (n+4)), sym (a (n+5)), sym (a (n+6)), sym (a (n+7))]

/-- The window premises: the k6 windows (`Windows6`) and the H8 step windows. -/
structure Windows6S (T : Tables6S) (d a : Nat → Nat) (m : Nat) : Prop where
  k6 : Windows6 T.k6 d a m
  h8 : ∀ j, j + 8 ≤ m → wforbH8 T (win8s6 d j)
    [sym (a (j+2)), sym (a (j+3)), sym (a (j+4)), sym (a (j+5)), sym (a (j+6)), sym (a (j+7))] = false

theorem step6S (T : Tables6S) (hT : StepOK6S T) (d a : Nat → Nat) (i : Nat)
    (h2 : 1 ≤ a (i+2)) (h3 : 1 ≤ a (i+3)) (h4 : 1 ≤ a (i+4)) (h5 : 1 ≤ a (i+5))
    (h6 : 1 ≤ a (i+6)) (h7 : 1 ≤ a (i+7))
    (hind : inducedPattern (win8s6 d i) = true)
    (hw2 : wforb6 T.k6 [d (i+5), d (i+6), d (i+7)] [sym (a (i+6)), sym (a (i+7))] = false)
    (hw3 : wforb6 T.k6 [d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false)
    (hw4 : wforb6 T.k6 [d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+4)), sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false)
    (hw5 : wforb6 T.k6 [d (i+2), d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false)
    (hw6 : wforb6 T.k6 [d (i+1), d (i+2), d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+2)), sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6)),
        sym (a (i+7))] = false)
    (hh8 : wforbH8 T (win8s6 d i)
      [sym (a (i+2)), sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6)),
        sym (a (i+7))] = false) :
    T.k6.num + Ψ6 T.k6 d a (i+1) ≤ T.k6.den * w6S T d a i + Ψ6 T.k6 d a i :=
  step6S_raw T hT (win8s6 d i) rfl (a (i+2)) (a (i+3)) (a (i+4)) (a (i+5)) (a (i+6)) (a (i+7))
    h2 h3 h4 h5 h6 h7 hind hw2 hw3 hw4 hw5 hw6 hh8

theorem invariant6S (T : Tables6S) (hT : StepOK6S T) (d a : Nat → Nat) (m : Nat)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + 8 ≤ m → inducedPattern (win8s6 d i) = true)
    (hw : Windows6S T d a m) :
    ∀ n, n + 7 ≤ m →
      T.k6.num * n + Ψ6 T.k6 d a n ≤ T.k6.den * Combined.rsum (w6S T d a) n + Ψ6 T.k6 d a 0
  | 0, _ => by simp [Combined.rsum]
  | n + 1, hn => by
    have ih := invariant6S T hT d a m hpos hind hw n (by omega)
    have hs := step6S T hT d a n (hpos (n+2) (by omega) (by omega))
      (hpos (n+3) (by omega) (by omega)) (hpos (n+4) (by omega) (by omega))
      (hpos (n+5) (by omega) (by omega)) (hpos (n+6) (by omega) (by omega))
      (hpos (n+7) (by omega) (by omega)) (hind n (by omega))
      (hw.k6.w2 (n+5) (by omega)) (hw.k6.w3 (n+4) (by omega)) (hw.k6.w4 (n+3) (by omega))
      (hw.k6.w5 (n+2) (by omega)) (hw.k6.w6 (n+1) (by omega)) (hw.h8 n (by omega))
    simp only [Combined.rsum, Nat.mul_succ, Nat.mul_add]
    omega

/-- The telescoped share-weighted inequality of an `m`-edge path (`m ≥ 7`):
`num (m - 7) ≤ den Σ_{n < m-7} (120 sym a(n+7) + S5 n) + (2^bits - 1)`, the premise `htel` of
`Combined.combined_bound`. -/
theorem total_bound6S (T : Tables6S) (hT : StepOK6S T) (d a : Nat → Nat) (m : Nat) (hm : 7 ≤ m)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + 8 ≤ m → inducedPattern (win8s6 d i) = true)
    (hw : Windows6S T d a m) :
    T.k6.num * (m - 7) ≤ T.k6.den * Combined.rsum (w6S T d a) (m - 7) + (2 ^ T.k6.bits - 1) := by
  have hinv := invariant6S T hT d a m hpos hind hw (m - 7) (by omega)
  have h0 := Ψ6_le T.k6 d a 0
  omega

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.check6S_of_shards
#print axioms Snake9.WindowAutomaton.stepOK6S_of_trivial
#print axioms Snake9.WindowAutomaton.total_bound6S
