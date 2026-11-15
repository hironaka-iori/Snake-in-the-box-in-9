/-
Share-weighted six-centre automaton with context shares (milestone 35, toward 231): definitions
and the sequence bound.

Core Lean only.  A copy of `WindowAutomaton6SDefs` (which stays unchanged for the audited 233
chain) in which the share level of a step may also come from a **context share threshold**
(milestones/28-combined-identities/share7.py):

* the automaton, its state and its step are those of `WindowAutomaton6SDefs`: state the canonical
  7-direction shape `d(n..n+6)` and the counts `a(n+2..n+6)`, step one more direction `d(n+7)` and
  count `s = a(n+7)`; so a transition knows the eight directions `c = d(n..n+7)` and the six counts
  `t = [t0, t1, t2, t3, t4, s] = a(n+2..n+7)`, i.e. everything a ctx 7 or ctx 8 record reads (the
  count at `n+1`, which ctx 8 leaves free, is not needed);
* `S5C T c t = max (share6 (c.drop 2) t.tail) (max (ctx7A (c.drop 1) t) (ctx8A c t))`:
  - `share6`: the 5-window share table of `T.s` (both orientations), unchanged;
  - `ctx7A T ds t`: field of the ctx 7 table at the canonical shape of the 7 directions
    `ds = d(n+1..n+7)` and the six counts `t` (one orientation only);
  - `ctx8A T ds t`: field of the ctx 8 table at the canonical shape of the 8 directions
    `ds = d(n..n+7)` and the six counts `t` (one orientation only);
  each is a lower bound of the M = 12 share sum of the trailing centres `n+3..n+7`
  (`DirectionWindowBridge6SC`), so the arithmetic of `CombinedShareToy.combined_bound` is unchanged;
* `check6SCAt T c t0`: `check6SAt` with `S5C` in place of `share6`;
* `total_bound6SC`: `num (m - 7) ≤ den Σ_{n < m-7} (120 sym a(n+7) + S5C n) + (2^bits - 1)`.
-/
import WindowAutomaton6SDefs

namespace Snake9.WindowAutomaton

/-- Tables of a share-weighted six-centre automaton with context shares. -/
structure Tables6SC where
  s : Tables6S
  /-- 7-direction shape code ↦ ctx 7 row -/
  c7Idx : Nat → Nat
  /-- ctx 7 row, first count `t0` ↦ `cbits`-wide fields at `cntIdx6 [t1, t2, t3, t4, s]` -/
  c7 : Nat → Nat → Nat
  /-- 8-direction shape code ↦ ctx 8 row -/
  c8Idx : Nat → Nat
  /-- ctx 8 row, first counted count `t0` (vertex `n+2`) ↦ fields at `cntIdx6 [t1, t2, t3, t4, s]` -/
  c8 : Nat → Nat → Nat
  cbits : Nat

/-- The `bits`-wide field of the row family `row` at the counts `t0 :: rest`. -/
def ctxAt (bits : Nat) (row : Nat → Nat) : List Nat → Nat
  | [] => 0
  | t0 :: rest => (row t0 >>> (bits * cntIdx6 rest 0)) &&& (2 ^ bits - 1)

/-- ctx 7 level of the 7 directions `ds` with the six counts `t` (oriented). -/
def ctx7A (T : Tables6SC) (ds t : List Nat) : Nat := ctxAt T.cbits (T.c7 (T.c7Idx (shapeCode (canon ds)))) t

/-- ctx 8 level of the 8 directions `ds` with the six counts `t` of the vertices 2..7 (oriented). -/
def ctx8A (T : Tables6SC) (ds t : List Nat) : Nat := ctxAt T.cbits (T.c8 (T.c8Idx (shapeCode (canon ds)))) t

/-- The share level of the step window `c` (8 directions) with the six counts `t`. -/
def S5C (T : Tables6SC) (c t : List Nat) : Nat :=
  max (share6 T.s (c.drop 2) t.tail) (max (ctx7A T (c.drop 1) t) (ctx8A T c t))

theorem share6_le_S5C (T : Tables6SC) (c : List Nat) (t0 : Nat) (t : List Nat) :
    share6 T.s (c.drop 2) t ≤ S5C T c (t0 :: t) := Nat.le_max_left _ _

theorem ctx7A_le_S5C (T : Tables6SC) (c t : List Nat) : ctx7A T (c.drop 1) t ≤ S5C T c t :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem ctx8A_le_S5C (T : Tables6SC) (c t : List Nat) : ctx8A T c t ≤ S5C T c t :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- Step test of the eight-direction window `c` from the states with first count `t0`. -/
def check6SCAt (T : Tables6SC) (c : List Nat) (t0 : Nat) : Bool :=
  !inducedPattern c ||
  allSym (fun t1 => allSym (fun t2 => allSym (fun t3 => allSym (fun t4 => allSym (fun s =>
    wforb6 T.s.k6 (c.drop 5) [t4, s] || wforb6 T.s.k6 (c.drop 4) [t3, t4, s] ||
    wforb6 T.s.k6 (c.drop 3) [t2, t3, t4, s] || wforb6 T.s.k6 (c.drop 2) [t1, t2, t3, t4, s] ||
    wforb6 T.s.k6 (c.drop 1) [t0, t1, t2, t3, t4, s] ||
    wforbH8 T.s c [t0, t1, t2, t3, t4, s] ||
    decide (T.s.k6.num + pot6 T.s.k6 (c.drop 1) [t1, t2, t3, t4, s] ≤
      T.s.k6.den * (120 * s + S5C T c [t0, t1, t2, t3, t4, s]) +
        pot6 T.s.k6 (c.take 7) [t0, t1, t2, t3, t4]))))))

/-- The step test holds for every canonical eight-direction window and first count. -/
def StepOK6SC (T : Tables6SC) : Prop :=
  ∀ c : List Nat, c.length = 8 → isRGS c 0 = true → ∀ t0, 1 ≤ t0 → t0 ≤ 6 →
    check6SCAt T c t0 = true

/-- What the shards prove. -/
def ShardsOK6SC (T : Tables6SC) (shapes : List (List Nat)) : Prop :=
  ∀ h ∈ shapes, ∀ t0, 1 ≤ t0 → t0 ≤ 6 → allBelow 9 (fun d => check6SCAt T (h ++ [d]) t0) = true

theorem check6SC_of_shards (T : Tables6SC) (shapes : List (List Nat)) (hr : ShapesCover shapes = true)
    (hs : ShardsOK6SC T shapes) : StepOK6SC T := by
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
  · unfold check6SCAt
    simp [hind]

/-- A table with zero potential and `num ≤ 120 den` passes every step test (toy instances). -/
theorem stepOK6SC_of_trivial (T : Tables6SC) (hp : ∀ r t, T.s.k6.pot r t = 0)
    (hnd : T.s.k6.num ≤ 120 * T.s.k6.den) : StepOK6SC T := by
  intro c _ _ t0 _ _
  unfold check6SCAt
  have hz : ∀ h t, pot6 T.s.k6 h t = 0 := by
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
  have h1 : 120 ≤ 120 * s + S5C T c [t0, t1, t2, t3, t4, s] := by omega
  have := Nat.mul_le_mul_left T.s.k6.den h1
  omega

/-! ### Transport: the step test applies to an arbitrary window -/

theorem ctx7A_canon_drop (T : Tables6SC) (ds t : List Nat) (n : Nat) :
    ctx7A T ((canon ds).drop n) t = ctx7A T (ds.drop n) t := by
  unfold ctx7A
  rw [canon_canon_drop]

theorem ctx8A_canon (T : Tables6SC) (ds t : List Nat) : ctx8A T (canon ds) t = ctx8A T ds t := by
  unfold ctx8A
  have h := canon_canon_drop ds 0
  simp only [List.drop_zero] at h
  rw [h]

theorem S5C_canon (T : Tables6SC) (ds t : List Nat) : S5C T (canon ds) t = S5C T ds t := by
  unfold S5C
  rw [share6_canon_drop, ctx7A_canon_drop, ctx8A_canon]

/-- The step inequality for an arbitrary eight-direction window. -/
theorem step6SC_raw (T : Tables6SC) (hT : StepOK6SC T) (x : List Nat) (hx : x.length = 8)
    (t0 t1 t2 t3 t4 s : Nat)
    (h0 : 1 ≤ t0) (h1 : 1 ≤ t1) (h2 : 1 ≤ t2) (h3 : 1 ≤ t3) (h4 : 1 ≤ t4) (hs : 1 ≤ s)
    (hind : inducedPattern x = true)
    (hw2 : wforb6 T.s.k6 (x.drop 5) [sym t4, sym s] = false)
    (hw3 : wforb6 T.s.k6 (x.drop 4) [sym t3, sym t4, sym s] = false)
    (hw4 : wforb6 T.s.k6 (x.drop 3) [sym t2, sym t3, sym t4, sym s] = false)
    (hw5 : wforb6 T.s.k6 (x.drop 2) [sym t1, sym t2, sym t3, sym t4, sym s] = false)
    (hw6 : wforb6 T.s.k6 (x.drop 1) [sym t0, sym t1, sym t2, sym t3, sym t4, sym s] = false)
    (hh8 : wforbH8 T.s x [sym t0, sym t1, sym t2, sym t3, sym t4, sym s] = false) :
    T.s.k6.num + pot6 T.s.k6 (x.drop 1) [sym t1, sym t2, sym t3, sym t4, sym s] ≤
      T.s.k6.den * (120 * sym s + S5C T x [sym t0, sym t1, sym t2, sym t3, sym t4, sym s]) +
        pot6 T.s.k6 (x.take 7) [sym t0, sym t1, sym t2, sym t3, sym t4] := by
  have hc := hT (canon x) (by rw [length_canon, hx]) (canon_isRGS x) (sym t0)
    (sym_ge_one _ h0) (sym_le_six _)
  unfold check6SCAt at hc
  rw [inducedPattern_canon, hind] at hc
  simp only [Bool.not_true, Bool.false_or] at hc
  have h := allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ hc
    (sym t1) (sym_ge_one _ h1) (sym_le_six _)) (sym t2) (sym_ge_one _ h2) (sym_le_six _))
    (sym t3) (sym_ge_one _ h3) (sym_le_six _)) (sym t4) (sym_ge_one _ h4) (sym_le_six _))
    (sym s) (sym_ge_one _ hs) (sym_le_six _)
  rw [wforb6_canon_drop, wforb6_canon_drop, wforb6_canon_drop, wforb6_canon_drop,
    wforb6_canon_drop, hw2, hw3, hw4, hw5, hw6, wforbH8_canon, hh8, pot6_canon_drop,
    pot6_canon_take, S5C_canon] at h
  simpa using h

/-! ### Sequence consequence -/

/-- The six counts of step `n`: `sym a(n+2) … sym a(n+7)`. -/
def syms6s6 (a : Nat → Nat) (n : Nat) : List Nat :=
  [sym (a (n+2)), sym (a (n+3)), sym (a (n+4)), sym (a (n+5)), sym (a (n+6)), sym (a (n+7))]

/-- The step weight of step `n`: `120 sym a(n+7)` plus the share level `S5C` of the step window
`d(n..n+7)` with the counts `a(n+2..n+7)`. -/
def w6SC (T : Tables6SC) (d a : Nat → Nat) (n : Nat) : Nat :=
  120 * sym (a (n+7)) + S5C T (win8s6 d n) (syms6s6 a n)

theorem step6SC (T : Tables6SC) (hT : StepOK6SC T) (d a : Nat → Nat) (i : Nat)
    (h2 : 1 ≤ a (i+2)) (h3 : 1 ≤ a (i+3)) (h4 : 1 ≤ a (i+4)) (h5 : 1 ≤ a (i+5))
    (h6 : 1 ≤ a (i+6)) (h7 : 1 ≤ a (i+7))
    (hind : inducedPattern (win8s6 d i) = true)
    (hw2 : wforb6 T.s.k6 [d (i+5), d (i+6), d (i+7)] [sym (a (i+6)), sym (a (i+7))] = false)
    (hw3 : wforb6 T.s.k6 [d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false)
    (hw4 : wforb6 T.s.k6 [d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+4)), sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false)
    (hw5 : wforb6 T.s.k6 [d (i+2), d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false)
    (hw6 : wforb6 T.s.k6 [d (i+1), d (i+2), d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+2)), sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6)),
        sym (a (i+7))] = false)
    (hh8 : wforbH8 T.s (win8s6 d i)
      [sym (a (i+2)), sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6)),
        sym (a (i+7))] = false) :
    T.s.k6.num + Ψ6 T.s.k6 d a (i+1) ≤ T.s.k6.den * w6SC T d a i + Ψ6 T.s.k6 d a i :=
  step6SC_raw T hT (win8s6 d i) rfl (a (i+2)) (a (i+3)) (a (i+4)) (a (i+5)) (a (i+6)) (a (i+7))
    h2 h3 h4 h5 h6 h7 hind hw2 hw3 hw4 hw5 hw6 hh8

theorem invariant6SC (T : Tables6SC) (hT : StepOK6SC T) (d a : Nat → Nat) (m : Nat)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + 8 ≤ m → inducedPattern (win8s6 d i) = true)
    (hw : Windows6S T.s d a m) :
    ∀ n, n + 7 ≤ m →
      T.s.k6.num * n + Ψ6 T.s.k6 d a n ≤ T.s.k6.den * Combined.rsum (w6SC T d a) n + Ψ6 T.s.k6 d a 0
  | 0, _ => by simp [Combined.rsum]
  | n + 1, hn => by
    have ih := invariant6SC T hT d a m hpos hind hw n (by omega)
    have hs := step6SC T hT d a n (hpos (n+2) (by omega) (by omega))
      (hpos (n+3) (by omega) (by omega)) (hpos (n+4) (by omega) (by omega))
      (hpos (n+5) (by omega) (by omega)) (hpos (n+6) (by omega) (by omega))
      (hpos (n+7) (by omega) (by omega)) (hind n (by omega))
      (hw.k6.w2 (n+5) (by omega)) (hw.k6.w3 (n+4) (by omega)) (hw.k6.w4 (n+3) (by omega))
      (hw.k6.w5 (n+2) (by omega)) (hw.k6.w6 (n+1) (by omega)) (hw.h8 n (by omega))
    simp only [Combined.rsum, Nat.mul_succ, Nat.mul_add]
    omega

/-- The telescoped inequality with context shares (`m ≥ 7`), the premise `htel` of
`Combined.combined_bound` with `S5 n = S5C T (win8s6 d n) (syms6s6 a n)`. -/
theorem total_bound6SC (T : Tables6SC) (hT : StepOK6SC T) (d a : Nat → Nat) (m : Nat) (hm : 7 ≤ m)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + 8 ≤ m → inducedPattern (win8s6 d i) = true)
    (hw : Windows6S T.s d a m) :
    T.s.k6.num * (m - 7) ≤ T.s.k6.den * Combined.rsum (w6SC T d a) (m - 7) + (2 ^ T.s.k6.bits - 1) := by
  have hinv := invariant6SC T hT d a m hpos hind hw (m - 7) (by omega)
  have h0 := Ψ6_le T.s.k6 d a 0
  omega

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.check6SC_of_shards
#print axioms Snake9.WindowAutomaton.stepOK6SC_of_trivial
#print axioms Snake9.WindowAutomaton.total_bound6SC
