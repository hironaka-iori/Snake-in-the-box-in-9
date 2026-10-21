/-
Six-centre (k = 6) direction automaton: generic definitions and the sequence bound.

Core Lean only.  Generalises `WindowAutomaton5R4Data` / `WindowAutomaton5R4Sequence`
(five centres: windows of 3..6 directions, states = 7-direction shape and 4 counts) to
six centres: windows of 3..7 directions (2..6 counts), states = 7-direction shape and 5
counts, so the state space is 34 * 6^5 = 264,384.

Everything is stated for an arbitrary table bundle `T : Tables6`; a generated data module
(`milestones/23-k6-lean/scripts/gen_lean_automaton6.py`) supplies the concrete tables and
the kernel-checked shards, and this module turns them into the telescoped inequality

  `T.num * m + 6 * T.den ≤ T.den * Σ_{j=1}^{m-1} a j + 7 * T.num + (2^T.bits - 1)`

(`total_bound6`), the same leading constant as the five-centre chain.

* Window exclusions: the mask row of a window is selected by its canonical shape code and
  its FIRST lumped count (`forbBit6`); the bit is `symIdx` of the remaining counts.  For a
  7-direction window this keeps every mask at 7^5 bits, as for the 6-direction windows of
  the five-centre tables.
* Potential: the row of a state is selected by its 7-shape code and its first count
  (`potAt6`); the field is `T.bits` wide at position `cntIdx6` of the other four counts.
  So a shard (7-shape, first count) reads one row of 6^4 fields, as a k5 shard does.
* `check6At T c t0`: the step test of the eight-direction window `c` from every state with
  first count `t0`; `StepOK T` is the statement proved by the 204 shards
  (`check6_of_shards`).
-/
import WindowAutomatonSequence

namespace Snake9.WindowAutomaton

/-- Tables of a six-centre automaton with `lambda = num / den`. -/
structure Tables6 where
  /-- window shape code ↦ exclusion row -/
  wIdx : Nat → Nat
  /-- exclusion row, first count ↦ mask over `symIdx` of the remaining counts -/
  forb : Nat → Nat → Nat
  /-- 7-shape code ↦ potential row -/
  pIdx : Nat → Nat
  /-- potential row, first count ↦ `bits`-wide fields at `cntIdx6` of the other counts -/
  pot : Nat → Nat → Nat
  bits : Nat
  num : Nat
  den : Nat

/-- Base-6 index of a count list (counts 1..6). -/
def cntIdx6 : List Nat → Nat → Nat
  | [], acc => acc
  | s :: l, acc => cntIdx6 l (acc * 6 + (s - 1))

/-- Exclusion bit of the window with shape code `code` and lumped counts `syms`. -/
def forbBit6 (T : Tables6) (code : Nat) : List Nat → Bool
  | [] => false
  | s :: rest => (T.forb (T.wIdx code) s >>> symIdx rest 0) &&& 1 == 1

def wforbA6 (T : Tables6) (ds syms : List Nat) : Bool := forbBit6 T (shapeCode (canon ds)) syms

/-- A window is excluded in either orientation. -/
def wforb6 (T : Tables6) (ds syms : List Nat) : Bool :=
  wforbA6 T ds syms || wforbA6 T ds.reverse syms.reverse

/-- Potential of the state with 7-shape code `code` and counts `t`. -/
def potAt6 (T : Tables6) (code : Nat) : List Nat → Nat
  | [] => 0
  | t0 :: rest => (T.pot (T.pIdx code) t0 >>> (T.bits * cntIdx6 rest 0)) &&& (2 ^ T.bits - 1)

def pot6 (T : Tables6) (h t : List Nat) : Nat := potAt6 T (shapeCode (canon h)) t

theorem pot6_le (T : Tables6) (h t : List Nat) : pot6 T h t ≤ 2 ^ T.bits - 1 := by
  unfold pot6
  cases t with
  | nil => exact Nat.zero_le _
  | cons t0 rest => exact Nat.and_le_right

/-- Step test for the eight-direction window `c` from the states with first count `t0`:
either a window of 3..7 directions ending at the new vertex is excluded, or the potential
drops by at least `num - den * s`. -/
def check6At (T : Tables6) (c : List Nat) (t0 : Nat) : Bool :=
  !inducedPattern c ||
  allSym (fun t1 => allSym (fun t2 => allSym (fun t3 => allSym (fun t4 => allSym (fun s =>
    wforb6 T (c.drop 5) [t4, s] || wforb6 T (c.drop 4) [t3, t4, s] ||
    wforb6 T (c.drop 3) [t2, t3, t4, s] || wforb6 T (c.drop 2) [t1, t2, t3, t4, s] ||
    wforb6 T (c.drop 1) [t0, t1, t2, t3, t4, s] ||
    decide (T.num + pot6 T (c.drop 1) [t1, t2, t3, t4, s] ≤
      T.den * s + pot6 T (c.take 7) [t0, t1, t2, t3, t4]))))))

/-- The step test holds for every canonical eight-direction window and first count. -/
def StepOK (T : Tables6) : Prop :=
  ∀ c : List Nat, c.length = 8 → isRGS c 0 = true → ∀ t0, 1 ≤ t0 → t0 ≤ 6 → check6At T c t0 = true

/-- What the shards prove: every listed 7-shape, extended by a label below 9, from every
first count. -/
def ShardsOK (T : Tables6) (shapes : List (List Nat)) : Prop :=
  ∀ h ∈ shapes, ∀ t0, 1 ≤ t0 → t0 ≤ 6 → allBelow 9 (fun d => check6At T (h ++ [d]) t0) = true

/-- The kernel-checked membership statement: every induced restricted growth string of
length 8 is a listed 7-shape followed by a label below 9. -/
def shapeTest6 (shapes : List (List Nat)) (c : List Nat) : Bool :=
  !inducedPattern c || (decide (c.take 7 ∈ shapes) && (c.drop 7).all (· < 9))

def ShapesCover (shapes : List (List Nat)) : Bool := allRGS 8 0 (shapeTest6 shapes)

/-! ### Splitting an `allRGS` check by prefixes

One kernel evaluation of `ShapesCover` (4,140 strings) needs more than 2.5 GB; it is split
into one declaration per restricted growth prefix (of length 5 in the generated modules). -/

/-- The label bound after a restricted growth prefix. -/
def rgsBound : List Nat → Nat → Nat
  | [], m => m
  | a :: l, m => rgsBound l (if m < a + 1 then a + 1 else m)

theorem allBelow_of_forall : ∀ n (p : Nat → Bool), (∀ a, a < n → p a = true) → allBelow n p = true
  | 0, _, _ => rfl
  | n + 1, p, h => by
    simp only [allBelow, Bool.and_eq_true]
    exact ⟨allBelow_of_forall n p (fun a ha => h a (by omega)), h n (by omega)⟩

theorem allRGS_of_forall : ∀ n m (p : List Nat → Bool),
    (∀ l, l.length = n → isRGS l m = true → p l = true) → allRGS n m p = true
  | 0, _, p, h => h [] rfl rfl
  | n + 1, m, p, h => by
    simp only [allRGS]
    refine allBelow_of_forall _ _ (fun a ha => allRGS_of_forall n _ _ (fun l hl hr => h (a :: l)
      (by simp [hl]) ?_))
    simp only [isRGS, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, hr⟩

theorem allRGS_split : ∀ k n m (p : List Nat → Bool), (∀ pre, pre.length = k → isRGS pre m = true →
    allRGS n (rgsBound pre m) (fun l => p (pre ++ l)) = true) → allRGS (k + n) m p = true
  | 0, n, m, p, h => by
    have := h [] rfl rfl
    simpa [rgsBound] using this
  | k + 1, n, m, p, h => by
    rw [show k + 1 + n = (k + n) + 1 by omega]
    simp only [allRGS]
    refine allBelow_of_forall _ _ (fun a ha => allRGS_split k n _ _ (fun pre hl hr => ?_))
    have := h (a :: pre) (by simp [hl]) (by
      simp only [isRGS, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, hr⟩)
    simpa [rgsBound] using this

/-- `ShapesCover` from one check per restricted growth prefix of length `k` (`pres` lists
them; the membership test is a cheap kernel evaluation). -/
theorem shapesCover_of (shapes pres : List (List Nat)) (k n : Nat) (hkn : k + n = 8)
    (hp : allRGS k 0 (fun pre => decide (pre ∈ pres)) = true)
    (h : ∀ pre ∈ pres, allRGS n (rgsBound pre 0) (fun l => shapeTest6 shapes (pre ++ l)) = true) :
    ShapesCover shapes = true := by
  unfold ShapesCover
  rw [← hkn]
  exact allRGS_split k n 0 _ (fun pre hl hr => h pre (of_decide_eq_true (allRGS_spec k 0 _ hp pre hl hr)))

theorem check6_of_shards (T : Tables6) (shapes : List (List Nat)) (hr : ShapesCover shapes = true)
    (hs : ShardsOK T shapes) : StepOK T := by
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
  · unfold check6At
    simp [hind]

/-- `allSym` from its six values (used by generated sequence modules). -/
theorem allSym_of_forall (f : Nat → Bool) (h : ∀ s, 1 ≤ s → s ≤ 6 → f s = true) :
    allSym f = true := by
  unfold allSym
  simp only [allBelow, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨trivial, h 1 (by omega) (by omega)⟩, h 2 (by omega) (by omega)⟩,
    h 3 (by omega) (by omega)⟩, h 4 (by omega) (by omega)⟩, h 5 (by omega) (by omega)⟩,
    h 6 (by omega) (by omega)⟩

/-- `allBelow 9` from its nine values: a shard module checks each label `d` in a theorem of
its own (the kernel's caches are per declaration, so the peak memory is that of one label). -/
theorem allBelow9_of (f : Nat → Bool) (h0 : f 0 = true) (h1 : f 1 = true) (h2 : f 2 = true)
    (h3 : f 3 = true) (h4 : f 4 = true) (h5 : f 5 = true) (h6 : f 6 = true) (h7 : f 7 = true)
    (h8 : f 8 = true) : allBelow 9 f = true := by
  simp only [allBelow, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨trivial, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩

/-- A table with zero potential and `num ≤ den` passes every step test (toy instances). -/
theorem stepOK_of_trivial (T : Tables6) (hp : ∀ r t, T.pot r t = 0) (hnd : T.num ≤ T.den) :
    StepOK T := by
  intro c _ _ t0 _ _
  unfold check6At
  have hz : ∀ h t, pot6 T h t = 0 := by
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
  have : T.den * 1 ≤ T.den * s := Nat.mul_le_mul_left _ hs
  omega

/-! ### Transport: the step test applies to an arbitrary window -/

theorem wforb6_canon_drop (T : Tables6) (ds syms : List Nat) (n : Nat) :
    wforb6 T ((canon ds).drop n) syms = wforb6 T (ds.drop n) syms := by
  unfold wforb6 wforbA6
  rw [canon_canon_drop, canon_canon_drop_reverse]

theorem pot6_canon_drop (T : Tables6) (ds t : List Nat) (n : Nat) :
    pot6 T ((canon ds).drop n) t = pot6 T (ds.drop n) t := by
  unfold pot6
  rw [canon_canon_drop]

theorem pot6_canon_take (T : Tables6) (ds t : List Nat) (n : Nat) :
    pot6 T ((canon ds).take n) t = pot6 T (ds.take n) t := by
  unfold pot6
  rw [canon_canon_take]

/-- The step inequality for an arbitrary eight-direction window. -/
theorem step6_raw (T : Tables6) (hT : StepOK T) (x : List Nat) (hx : x.length = 8)
    (t0 t1 t2 t3 t4 s : Nat)
    (h0 : 1 ≤ t0) (h1 : 1 ≤ t1) (h2 : 1 ≤ t2) (h3 : 1 ≤ t3) (h4 : 1 ≤ t4) (hs : 1 ≤ s)
    (hind : inducedPattern x = true)
    (hw2 : wforb6 T (x.drop 5) [sym t4, sym s] = false)
    (hw3 : wforb6 T (x.drop 4) [sym t3, sym t4, sym s] = false)
    (hw4 : wforb6 T (x.drop 3) [sym t2, sym t3, sym t4, sym s] = false)
    (hw5 : wforb6 T (x.drop 2) [sym t1, sym t2, sym t3, sym t4, sym s] = false)
    (hw6 : wforb6 T (x.drop 1) [sym t0, sym t1, sym t2, sym t3, sym t4, sym s] = false) :
    T.num + pot6 T (x.drop 1) [sym t1, sym t2, sym t3, sym t4, sym s] ≤
      T.den * sym s + pot6 T (x.take 7) [sym t0, sym t1, sym t2, sym t3, sym t4] := by
  have hc := hT (canon x) (by rw [length_canon, hx]) (canon_isRGS x) (sym t0)
    (sym_ge_one _ h0) (sym_le_six _)
  unfold check6At at hc
  rw [inducedPattern_canon, hind] at hc
  simp only [Bool.not_true, Bool.false_or] at hc
  have h := allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ hc
    (sym t1) (sym_ge_one _ h1) (sym_le_six _)) (sym t2) (sym_ge_one _ h2) (sym_le_six _))
    (sym t3) (sym_ge_one _ h3) (sym_le_six _)) (sym t4) (sym_ge_one _ h4) (sym_le_six _))
    (sym s) (sym_ge_one _ hs) (sym_le_six _)
  rw [wforb6_canon_drop, wforb6_canon_drop, wforb6_canon_drop, wforb6_canon_drop,
    wforb6_canon_drop, hw2, hw3, hw4, hw5, hw6, pot6_canon_drop, pot6_canon_take] at h
  simpa using h

/-! ### Sequence consequence -/

def win8s6 (d : Nat → Nat) (i : Nat) : List Nat :=
  [d i, d (i+1), d (i+2), d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]

def hist7s6 (d : Nat → Nat) (i : Nat) : List Nat :=
  [d i, d (i+1), d (i+2), d (i+3), d (i+4), d (i+5), d (i+6)]

def syms5s6 (a : Nat → Nat) (i : Nat) : List Nat :=
  [sym (a (i+2)), sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6))]

/-- Potential of the state after centre `i+6`. -/
def Ψ6 (T : Tables6) (d a : Nat → Nat) (i : Nat) : Nat := pot6 T (hist7s6 d i) (syms5s6 a i)

theorem Ψ6_le (T : Tables6) (d a : Nat → Nat) (i : Nat) : Ψ6 T d a i ≤ 2 ^ T.bits - 1 :=
  pot6_le _ _ _

theorem step6 (T : Tables6) (hT : StepOK T) (d a : Nat → Nat) (i : Nat)
    (h2 : 1 ≤ a (i+2)) (h3 : 1 ≤ a (i+3)) (h4 : 1 ≤ a (i+4)) (h5 : 1 ≤ a (i+5))
    (h6 : 1 ≤ a (i+6)) (h7 : 1 ≤ a (i+7))
    (hind : inducedPattern (win8s6 d i) = true)
    (hw2 : wforb6 T [d (i+5), d (i+6), d (i+7)] [sym (a (i+6)), sym (a (i+7))] = false)
    (hw3 : wforb6 T [d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false)
    (hw4 : wforb6 T [d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+4)), sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false)
    (hw5 : wforb6 T [d (i+2), d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false)
    (hw6 : wforb6 T [d (i+1), d (i+2), d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+2)), sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6)),
        sym (a (i+7))] = false) :
    T.num + Ψ6 T d a (i+1) ≤ T.den * sym (a (i+7)) + Ψ6 T d a i :=
  step6_raw T hT (win8s6 d i) rfl (a (i+2)) (a (i+3)) (a (i+4)) (a (i+5)) (a (i+6)) (a (i+7))
    h2 h3 h4 h5 h6 h7 hind hw2 hw3 hw4 hw5 hw6

/-- `S6 a n = Σ_{t<n} sym (a (t+7))`. -/
def S6 (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => S6 a n + sym (a (n+7))

/-- The window premises of the six-centre automaton (windows of 3 to 7 directions). -/
structure Windows6 (T : Tables6) (d a : Nat → Nat) (m : Nat) : Prop where
  w2 : ∀ j, j + 3 ≤ m → wforb6 T [d j, d (j+1), d (j+2)] [sym (a (j+1)), sym (a (j+2))] = false
  w3 : ∀ j, j + 4 ≤ m → wforb6 T [d j, d (j+1), d (j+2), d (j+3)]
    [sym (a (j+1)), sym (a (j+2)), sym (a (j+3))] = false
  w4 : ∀ j, j + 5 ≤ m → wforb6 T [d j, d (j+1), d (j+2), d (j+3), d (j+4)]
    [sym (a (j+1)), sym (a (j+2)), sym (a (j+3)), sym (a (j+4))] = false
  w5 : ∀ j, j + 6 ≤ m → wforb6 T [d j, d (j+1), d (j+2), d (j+3), d (j+4), d (j+5)]
    [sym (a (j+1)), sym (a (j+2)), sym (a (j+3)), sym (a (j+4)), sym (a (j+5))] = false
  w6 : ∀ j, j + 7 ≤ m → wforb6 T [d j, d (j+1), d (j+2), d (j+3), d (j+4), d (j+5), d (j+6)]
    [sym (a (j+1)), sym (a (j+2)), sym (a (j+3)), sym (a (j+4)), sym (a (j+5)),
      sym (a (j+6))] = false

theorem invariant6 (T : Tables6) (hT : StepOK T) (d a : Nat → Nat) (m : Nat)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + 8 ≤ m → inducedPattern (win8s6 d i) = true)
    (hw : Windows6 T d a m) :
    ∀ n, n + 7 ≤ m → T.num * n + Ψ6 T d a n ≤ T.den * S6 a n + Ψ6 T d a 0
  | 0, _ => by simp [S6]
  | n + 1, hn => by
    have ih := invariant6 T hT d a m hpos hind hw n (by omega)
    have hs := step6 T hT d a n (hpos (n+2) (by omega) (by omega)) (hpos (n+3) (by omega) (by omega))
      (hpos (n+4) (by omega) (by omega)) (hpos (n+5) (by omega) (by omega))
      (hpos (n+6) (by omega) (by omega)) (hpos (n+7) (by omega) (by omega)) (hind n (by omega))
      (hw.w2 (n+5) (by omega)) (hw.w3 (n+4) (by omega)) (hw.w4 (n+3) (by omega))
      (hw.w5 (n+2) (by omega)) (hw.w6 (n+1) (by omega))
    simp only [S6, Nat.mul_succ, Nat.mul_add]
    omega

theorem sumA_ge6 (a : Nat → Nat) (m : Nat) (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j) :
    ∀ n, n + 7 ≤ m → 6 + S6 a n ≤ sumA a (n + 6)
  | 0, h => by
    simp only [S6, sumA, Nat.zero_add, Nat.reduceAdd]
    have := hpos 1 (by omega) (by omega)
    have := hpos 2 (by omega) (by omega)
    have := hpos 3 (by omega) (by omega)
    have := hpos 4 (by omega) (by omega)
    have := hpos 5 (by omega) (by omega)
    have := hpos 6 (by omega) (by omega)
    omega
  | n + 1, h => by
    have ih := sumA_ge6 a m hpos n (by omega)
    have := sym_le (a (n+7))
    show 6 + (S6 a n + sym (a (n+7))) ≤ sumA a (n+6) + a (n+6+1)
    have he2 : n + 6 + 1 = n + 7 := by omega
    rw [he2]
    omega

/-- Internal counts of an `m`-edge path under the six-centre window exclusions:
`num m + 6 den ≤ den Σ_{j=1}^{m-1} a j + 7 num + (2^bits - 1)`. -/
theorem total_bound6 (T : Tables6) (hT : StepOK T) (d a : Nat → Nat) (m : Nat) (hm : 7 ≤ m)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + 8 ≤ m → inducedPattern (win8s6 d i) = true)
    (hw : Windows6 T d a m) :
    T.num * m + 6 * T.den ≤ T.den * sumA a (m - 1) + 7 * T.num + (2 ^ T.bits - 1) := by
  have hinv := invariant6 T hT d a m hpos hind hw (m - 7) (by omega)
  have hsum := sumA_ge6 a m hpos (m - 7) (by omega)
  have h0 := Ψ6_le T d a 0
  have he : m - 7 + 6 = m - 1 := by omega
  rw [he] at hsum
  have hmul := Nat.mul_le_mul_left T.den hsum
  have hm7 : T.num * m = T.num * (m - 7) + 7 * T.num := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 7 := ⟨m - 7, by omega⟩
    rw [show k + 7 - 7 = k by omega, Nat.mul_add, Nat.mul_comm T.num 7]
  rw [Nat.mul_add] at hmul
  omega

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.check6_of_shards
#print axioms Snake9.WindowAutomaton.total_bound6
