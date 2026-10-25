/-
Seven-centre (k = 7) direction automaton: generic definitions and the sequence bound.

Core Lean only.  Extends `WindowAutomaton6Defs` by one step of memory
(milestones/25-k7-234, section "Lean plan"):

* State: canonical 8-direction shape `d(i..i+7)` and six lumped counts `a(i+2..i+7)`;
  132 · 6^6 states.
* Step: one more direction `d(i+8)` and count `s = a(i+8)`; the step window `c` is the
  9-direction list `d(i..i+8)`.  Tested windows:
  - (k6) the windows of 3..7 directions ending at the new vertex (2..6 counts), both
    orientations, in the exclusion table of the k6 automaton (`wforb6`);
  - (F8) the 8-direction window `c.drop 1` with all seven counts `a(i+2..i+8)`, both
    orientations, in the same table;
  - (H9) the 9-direction window `c` with the seven counts `a(i+2..i+8)`, the first interior
    vertex `a(i+1)` uncounted.  Its key is stored reversed, so that the uncounted vertex is
    the last centre: `(canon (rev c), rev counts)`, whose certificate is literally
    `Refuted (winOf ds) (boundsOf syms)` with 7 bounds for 8 interior vertices.  The H9
    table is sparse (a few keys per row of 7^6 bits), so it is a binary search tree of
    base-9 codes (`NTree`, `wforbH`) instead of a mask table.
  - otherwise `num + pot(next) ≤ den·s + pot(current)` must hold.
* Closed-set skip (`own7`): a state whose own k6 windows (3..7 directions ending at its last
  vertex, counts from its six) are excluded never occurs in a snake, since those windows are
  windows of the snake.  `check7At` skips such states; `step7_raw` discharges the skip from
  the window premises at the state's own position.
* Potential rows are keyed by (8-shape code, t0, t1), with `bits`-wide fields at
  `cntIdx6 [t2..t5]` (6^4 fields per row).  A shard declaration (8-shape, label, t0, t1)
  reads one source row.

`total_bound7`:  `num·m + 7 den ≤ den · Σ_{j=1}^{m-1} a j + 8 num + (2^bits − 1)` for m ≥ 8.
-/
import WindowAutomaton6Defs

namespace Snake9.WindowAutomaton

/-! ### Sparse sets of naturals (the H9 table) -/

/-- A binary search tree of naturals.  Only `mem t x = true → x ∈ t.toList` is used, so
the search order is a matter of speed, not of soundness. -/
inductive NTree where
  | nil : NTree
  | node : NTree → Nat → NTree → NTree

def NTree.mem : NTree → Nat → Bool
  | .nil, _ => false
  | .node l v r, x => x == v || cond (Nat.blt x v) (l.mem x) (r.mem x)

def NTree.toList : NTree → List Nat
  | .nil => []
  | .node l v r => l.toList ++ v :: r.toList

theorem NTree.mem_toList : ∀ (t : NTree) (x : Nat), t.mem x = true → x ∈ t.toList
  | .nil, _, h => by simp [NTree.mem] at h
  | .node l v r, x, h => by
    simp only [NTree.mem, Bool.or_eq_true, beq_iff_eq] at h
    simp only [NTree.toList, List.mem_append, List.mem_cons]
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · cases hb : Nat.blt x v
      · rw [hb] at h
        exact Or.inr (Or.inr (NTree.mem_toList r x h))
      · rw [hb] at h
        exact Or.inl (NTree.mem_toList l x h)

/-- Base-`b` code of a digit list. -/
def encB (b : Nat) : List Nat → Nat → Nat
  | [], acc => acc
  | a :: l, acc => encB b l (acc * b + a)

/-! ### Tables -/

/-- Tables of a seven-centre automaton with `lambda = num / den`. -/
structure Tables7 where
  /-- window shape code (3 to 8 directions) ↦ exclusion row -/
  wIdx : Nat → Nat
  /-- exclusion row, first count ↦ mask over `symIdx` of the remaining counts -/
  forb : Nat → Nat → Nat
  /-- 8-shape code ↦ potential row -/
  pIdx : Nat → Nat
  /-- potential row, t0, t1 ↦ `bits`-wide fields at `cntIdx6 [t2, t3, t4, t5]` -/
  pot : Nat → Nat → Nat → Nat
  /-- H9 keys: `encB 9 (ds ++ syms) 0` of each key -/
  htree : NTree
  bits : Nat
  num : Nat
  den : Nat

/-- The exclusion part as a six-centre table bundle (its potential fields are unused), so
that `wforb6` and the k6 cover argument apply verbatim. -/
def Tables7.k6 (T : Tables7) : Tables6 where
  wIdx := T.wIdx
  forb := T.forb
  pIdx := fun _ => 0
  pot := fun _ _ => 0
  bits := 0
  num := 0
  den := 0

/-- H9 lookup of the window `ds` (9 directions) with counts `syms` (7 counts, the first
interior vertex uncounted), in the reversed key form. -/
def wforbH (T : Tables7) (ds syms : List Nat) : Bool :=
  T.htree.mem (encB 9 (canon ds.reverse ++ syms.reverse) 0)

/-- Potential of the state with 8-shape code `code` and counts `t = [t0, …, t5]`. -/
def potAt7 (T : Tables7) (code : Nat) : List Nat → Nat
  | t0 :: t1 :: rest =>
    (T.pot (T.pIdx code) t0 t1 >>> (T.bits * cntIdx6 rest 0)) &&& (2 ^ T.bits - 1)
  | _ => 0

def pot7 (T : Tables7) (h t : List Nat) : Nat := potAt7 T (shapeCode (canon h)) t

theorem pot7_le (T : Tables7) (h t : List Nat) : pot7 T h t ≤ 2 ^ T.bits - 1 := by
  unfold pot7
  match t with
  | [] => exact Nat.zero_le _
  | [_] => exact Nat.zero_le _
  | _ :: _ :: _ => exact Nat.and_le_right

/-- The own k6 windows of the state with 8-shape `h` and counts `t0..t5`: 3..7 directions
ending at its last vertex.  If one is excluded, the state never occurs in a snake. -/
def own7 (T : Tables7) (h : List Nat) (t0 t1 t2 t3 t4 t5 : Nat) : Bool :=
  wforb6 T.k6 (h.drop 5) [t4, t5] || wforb6 T.k6 (h.drop 4) [t3, t4, t5] ||
  wforb6 T.k6 (h.drop 3) [t2, t3, t4, t5] || wforb6 T.k6 (h.drop 2) [t1, t2, t3, t4, t5] ||
  wforb6 T.k6 (h.drop 1) [t0, t1, t2, t3, t4, t5]

/-- The step test of the nine-direction window `c` from the states with counts `t0, t1, t2`
(and all `t3..t5`), for every new count `s`: the source state is skipped by the closed-set
rule, or a k6/F8/H9 window ending at the new vertex is excluded, or the potential drops by
at least `num - den * s`: 6^4 transitions. -/
def check7In2 (T : Tables7) (c : List Nat) (t0 t1 t2 : Nat) : Bool :=
  allSym (fun t3 => allSym (fun t4 => allSym (fun t5 =>
    own7 T (c.take 8) t0 t1 t2 t3 t4 t5 || allSym (fun s =>
    wforb6 T.k6 (c.drop 6) [t5, s] || wforb6 T.k6 (c.drop 5) [t4, t5, s] ||
    wforb6 T.k6 (c.drop 4) [t3, t4, t5, s] || wforb6 T.k6 (c.drop 3) [t2, t3, t4, t5, s] ||
    wforb6 T.k6 (c.drop 2) [t1, t2, t3, t4, t5, s] ||
    wforb6 T.k6 (c.drop 1) [t0, t1, t2, t3, t4, t5, s] ||
    wforbH T c [t0, t1, t2, t3, t4, t5, s] ||
    decide (T.num + pot7 T (c.drop 1) [t1, t2, t3, t4, t5, s] ≤
      T.den * s + pot7 T (c.take 8) [t0, t1, t2, t3, t4, t5])))))

/-- The step test from the states with counts `t0, t1`; a shard checks it either in one
declaration (6^5 transitions) or in six, one per `t2` (`check7In_of`, 6^4 transitions each,
for a lower kernel peak). -/
def check7In (T : Tables7) (c : List Nat) (t0 t1 : Nat) : Bool :=
  allSym (fun t2 => check7In2 T c t0 t1 t2)

def check7At (T : Tables7) (c : List Nat) (t0 : Nat) : Bool :=
  !inducedPattern c || allSym (fun t1 => check7In T c t0 t1)

/-- The step test holds for every canonical nine-direction window and first count. -/
def StepOK7 (T : Tables7) : Prop :=
  ∀ c : List Nat, c.length = 9 → isRGS c 0 = true → ∀ t0, 1 ≤ t0 → t0 ≤ 6 →
    check7At T c t0 = true

/-- What the shards prove: every listed 8-shape `h`, extended by every restricted growth
label (at most `rgsBound h 0`), from every first count. -/
def ShardsOK7 (T : Tables7) (shapes : List (List Nat)) : Prop :=
  ∀ h ∈ shapes, ∀ t0, 1 ≤ t0 → t0 ≤ 6 →
    allBelow (rgsBound h 0 + 1) (fun d => check7At T (h ++ [d]) t0) = true

/-- Every induced restricted growth string of length 9 starts with a listed 8-shape. -/
def shapeTest7 (shapes : List (List Nat)) (c : List Nat) : Bool :=
  !inducedPattern c || decide (c.take 8 ∈ shapes)

def ShapesCover7 (shapes : List (List Nat)) : Bool := allRGS 9 0 (shapeTest7 shapes)

/-! ### Restricted growth strings and prefixes -/

theorem isRGS_append : ∀ (h l : List Nat) (m : Nat),
    isRGS (h ++ l) m = (isRGS h m && isRGS l (rgsBound h m))
  | [], l, m => by simp [isRGS, rgsBound]
  | a :: h, l, m => by
    simp only [List.cons_append, isRGS, rgsBound, Bool.and_assoc]
    rw [isRGS_append h l]

/-- `allRGS N 0 p` from one check per restricted growth prefix of length `k`. -/
theorem allRGS_of_prefixes (p : List Nat → Bool) (pres : List (List Nat)) (k n N : Nat)
    (hkn : k + n = N) (hp : allRGS k 0 (fun pre => decide (pre ∈ pres)) = true)
    (h : ∀ pre ∈ pres, allRGS n (rgsBound pre 0) (fun l => p (pre ++ l)) = true) :
    allRGS N 0 p = true := by
  rw [← hkn]
  exact allRGS_split k n 0 _ (fun pre hl hr => h pre (of_decide_eq_true (allRGS_spec k 0 _ hp pre hl hr)))

theorem allBelow_succ_of (n : Nat) (p : Nat → Bool) (h1 : allBelow n p = true) (h2 : p n = true) :
    allBelow (n + 1) p = true := by
  simp only [allBelow, Bool.and_eq_true]
  exact ⟨h1, h2⟩

/-- `check7At` from its six `t1` declarations (used by the generated shards). -/
theorem check7At_of (T : Tables7) (c : List Nat) (t0 : Nat) (h1 : check7In T c t0 1 = true)
    (h2 : check7In T c t0 2 = true) (h3 : check7In T c t0 3 = true)
    (h4 : check7In T c t0 4 = true) (h5 : check7In T c t0 5 = true)
    (h6 : check7In T c t0 6 = true) : check7At T c t0 = true := by
  unfold check7At
  refine Bool.or_eq_true_iff.2 (Or.inr (allSym_of_forall _ (fun t ht1 ht6 => ?_)))
  have : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

theorem check7In_of (T : Tables7) (c : List Nat) (t0 t1 : Nat)
    (h1 : check7In2 T c t0 t1 1 = true) (h2 : check7In2 T c t0 t1 2 = true)
    (h3 : check7In2 T c t0 t1 3 = true) (h4 : check7In2 T c t0 t1 4 = true)
    (h5 : check7In2 T c t0 t1 5 = true) (h6 : check7In2 T c t0 t1 6 = true) :
    check7In T c t0 t1 = true := by
  unfold check7In
  refine allSym_of_forall _ (fun t ht1 ht6 => ?_)
  have : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

theorem check7_of_shards (T : Tables7) (shapes : List (List Nat))
    (hr : ShapesCover7 shapes = true) (hs : ShardsOK7 T shapes) : StepOK7 T := by
  intro c hc hrgs t0 h1 h6
  have hm := allRGS_spec 9 0 _ hr c hc hrgs
  simp only [shapeTest7] at hm
  by_cases hind : inducedPattern c = true
  · rw [hind] at hm
    simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hm
    have hsplit : c = c.take 8 ++ c.drop 8 := (List.take_append_drop 8 c).symm
    have hlen : (c.drop 8).length = 1 := by simp [hc]
    obtain ⟨d, hd8⟩ : ∃ d, c.drop 8 = [d] := by
      match h : c.drop 8, hlen with
      | [d], _ => exact ⟨d, rfl⟩
    have hd : d < rgsBound (c.take 8) 0 + 1 := by
      have hr2 := hrgs
      rw [hsplit, hd8, isRGS_append] at hr2
      simp only [isRGS, Bool.and_eq_true, decide_eq_true_eq] at hr2
      omega
    rw [hsplit, hd8]
    exact allBelow_spec _ _ (hs _ hm t0 h1 h6) d hd
  · unfold check7At
    simp [hind]

/-- A table with zero potential and `num ≤ den` passes every step test (toy instances). -/
theorem stepOK7_of_trivial (T : Tables7) (hp : ∀ r t0 t1, T.pot r t0 t1 = 0) (hnd : T.num ≤ T.den) :
    StepOK7 T := by
  intro c _ _ t0 _ _
  have hz : ∀ h t, pot7 T h t = 0 := by
    intro h t
    unfold pot7
    match t with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ => simp only [potAt7, hp, Nat.zero_shiftRight, Nat.zero_and]
  unfold check7At
  refine Bool.or_eq_true_iff.2 (Or.inr (allSym_of_forall _ (fun t1 _ _ => ?_)))
  unfold check7In check7In2
  refine allSym_of_forall _ (fun t2 _ _ => allSym_of_forall _ (fun t3 _ _ =>
    allSym_of_forall _ (fun t4 _ _ => allSym_of_forall _ (fun t5 _ _ => ?_))))
  refine Bool.or_eq_true_iff.2 (Or.inr (allSym_of_forall _ (fun s hs _ => ?_)))
  simp only [hz, Nat.add_zero, Bool.or_eq_true, decide_eq_true_eq]
  right
  have : T.den * 1 ≤ T.den * s := Nat.mul_le_mul_left _ hs
  omega

/-! ### Transport: the step test applies to an arbitrary window -/

theorem canon_canon_take_drop (ds : List Nat) (n k : Nat) :
    canon (((canon ds).take n).drop k) = canon ((ds.take n).drop k) := by
  rw [canon_eq_map ds, ← List.map_take, ← List.map_drop]
  exact canon_map _ _ (label_inj_sub ds _
    (fun x hx => List.take_subset n ds (List.drop_subset k _ hx)))

theorem canon_canon_take_drop_reverse (ds : List Nat) (n k : Nat) :
    canon (((canon ds).take n).drop k).reverse = canon ((ds.take n).drop k).reverse := by
  rw [canon_eq_map ds, ← List.map_take, ← List.map_drop, ← List.map_reverse]
  exact canon_map _ _ (label_inj_sub ds _
    (fun x hx => List.take_subset n ds (List.drop_subset k _ (List.mem_reverse.mp hx))))

theorem canon_canon_reverse (ds : List Nat) : canon (canon ds).reverse = canon ds.reverse := by
  have := canon_canon_drop_reverse ds 0
  simpa using this

theorem wforb6_canon_take_drop (T : Tables6) (ds syms : List Nat) (n k : Nat) :
    wforb6 T (((canon ds).take n).drop k) syms = wforb6 T ((ds.take n).drop k) syms := by
  unfold wforb6 wforbA6
  rw [canon_canon_take_drop, canon_canon_take_drop_reverse]

theorem wforbH_canon (T : Tables7) (ds syms : List Nat) :
    wforbH T (canon ds) syms = wforbH T ds syms := by
  unfold wforbH
  rw [canon_canon_reverse]

theorem pot7_canon_drop (T : Tables7) (ds t : List Nat) (n : Nat) :
    pot7 T ((canon ds).drop n) t = pot7 T (ds.drop n) t := by
  unfold pot7
  rw [canon_canon_drop]

theorem pot7_canon_take (T : Tables7) (ds t : List Nat) (n : Nat) :
    pot7 T ((canon ds).take n) t = pot7 T (ds.take n) t := by
  unfold pot7
  rw [canon_canon_take]

/-- The step inequality for an arbitrary nine-direction window `x` from the state
`(x.take 8, t0..t5)` with new count `s`.  `hv2..hv6` are the own windows of the state (they
discharge the closed-set skip), `hw2..hw7` the k6/F8 windows ending at the new vertex,
`hwh` the H9 window. -/
theorem step7_raw (T : Tables7) (hT : StepOK7 T) (x : List Nat) (hx : x.length = 9)
    (t0 t1 t2 t3 t4 t5 s : Nat)
    (h0 : 1 ≤ t0) (h1 : 1 ≤ t1) (h2 : 1 ≤ t2) (h3 : 1 ≤ t3) (h4 : 1 ≤ t4) (h5 : 1 ≤ t5)
    (hs : 1 ≤ s) (hind : inducedPattern x = true)
    (hv2 : wforb6 T.k6 ((x.take 8).drop 5) [sym t4, sym t5] = false)
    (hv3 : wforb6 T.k6 ((x.take 8).drop 4) [sym t3, sym t4, sym t5] = false)
    (hv4 : wforb6 T.k6 ((x.take 8).drop 3) [sym t2, sym t3, sym t4, sym t5] = false)
    (hv5 : wforb6 T.k6 ((x.take 8).drop 2) [sym t1, sym t2, sym t3, sym t4, sym t5] = false)
    (hv6 : wforb6 T.k6 ((x.take 8).drop 1)
      [sym t0, sym t1, sym t2, sym t3, sym t4, sym t5] = false)
    (hw2 : wforb6 T.k6 (x.drop 6) [sym t5, sym s] = false)
    (hw3 : wforb6 T.k6 (x.drop 5) [sym t4, sym t5, sym s] = false)
    (hw4 : wforb6 T.k6 (x.drop 4) [sym t3, sym t4, sym t5, sym s] = false)
    (hw5 : wforb6 T.k6 (x.drop 3) [sym t2, sym t3, sym t4, sym t5, sym s] = false)
    (hw6 : wforb6 T.k6 (x.drop 2) [sym t1, sym t2, sym t3, sym t4, sym t5, sym s] = false)
    (hw7 : wforb6 T.k6 (x.drop 1)
      [sym t0, sym t1, sym t2, sym t3, sym t4, sym t5, sym s] = false)
    (hwh : wforbH T x [sym t0, sym t1, sym t2, sym t3, sym t4, sym t5, sym s] = false) :
    T.num + pot7 T (x.drop 1) [sym t1, sym t2, sym t3, sym t4, sym t5, sym s] ≤
      T.den * sym s + pot7 T (x.take 8) [sym t0, sym t1, sym t2, sym t3, sym t4, sym t5] := by
  have hc := hT (canon x) (by rw [length_canon, hx]) (canon_isRGS x) (sym t0)
    (sym_ge_one _ h0) (sym_le_six _)
  unfold check7At at hc
  rw [inducedPattern_canon, hind] at hc
  simp only [Bool.not_true, Bool.false_or] at hc
  have hi := allSym_spec _ hc (sym t1) (sym_ge_one _ h1) (sym_le_six _)
  unfold check7In check7In2 at hi
  have h := allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ hi
    (sym t2) (sym_ge_one _ h2) (sym_le_six _)) (sym t3) (sym_ge_one _ h3) (sym_le_six _))
    (sym t4) (sym_ge_one _ h4) (sym_le_six _)) (sym t5) (sym_ge_one _ h5) (sym_le_six _)
  simp only [own7, wforb6_canon_take_drop, hv2, hv3, hv4, hv5, hv6, Bool.false_or] at h
  have h' := allSym_spec _ h (sym s) (sym_ge_one _ hs) (sym_le_six _)
  simp only [wforb6_canon_drop, wforbH_canon, pot7_canon_drop, pot7_canon_take,
    hw2, hw3, hw4, hw5, hw6, hw7, hwh, Bool.false_or, decide_eq_true_eq] at h'
  exact h'

/-! ### Sequence consequence -/

def win9s7 (d : Nat → Nat) (i : Nat) : List Nat :=
  [d i, d (i+1), d (i+2), d (i+3), d (i+4), d (i+5), d (i+6), d (i+7), d (i+8)]

def hist8s7 (d : Nat → Nat) (i : Nat) : List Nat :=
  [d i, d (i+1), d (i+2), d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]

def syms6s7 (a : Nat → Nat) (i : Nat) : List Nat :=
  [sym (a (i+2)), sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6)), sym (a (i+7))]

/-- Potential of the state after centre `i+7`. -/
def Ψ7 (T : Tables7) (d a : Nat → Nat) (i : Nat) : Nat := pot7 T (hist8s7 d i) (syms6s7 a i)

theorem Ψ7_le (T : Tables7) (d a : Nat → Nat) (i : Nat) : Ψ7 T d a i ≤ 2 ^ T.bits - 1 :=
  pot7_le _ _ _

/-- The window premises of the seven-centre automaton: the k6 windows (3 to 7 directions),
the F8 windows (8 directions, 7 counts) and the H9 windows (9 directions, the counts of the
last seven interior vertices). -/
structure Windows7 (T : Tables7) (d a : Nat → Nat) (m : Nat) : Prop where
  w6 : Windows6 T.k6 d a m
  w7 : ∀ j, j + 8 ≤ m → wforb6 T.k6 [d j, d (j+1), d (j+2), d (j+3), d (j+4), d (j+5), d (j+6),
    d (j+7)] [sym (a (j+1)), sym (a (j+2)), sym (a (j+3)), sym (a (j+4)), sym (a (j+5)),
      sym (a (j+6)), sym (a (j+7))] = false
  wh : ∀ j, j + 9 ≤ m → wforbH T [d j, d (j+1), d (j+2), d (j+3), d (j+4), d (j+5), d (j+6),
    d (j+7), d (j+8)] [sym (a (j+2)), sym (a (j+3)), sym (a (j+4)), sym (a (j+5)),
      sym (a (j+6)), sym (a (j+7)), sym (a (j+8))] = false

/-- Soundness of the closed-set skip: in a sequence satisfying the k6 window premises, the
own windows of every state are not excluded, so `own7` is false on every state that occurs
(the state at `i` is `(d(i..i+7), a(i+2..i+7))`, including `i = 0`). -/
theorem own7_false (T : Tables7) (d a : Nat → Nat) (m : Nat) (hw : Windows6 T.k6 d a m)
    (i : Nat) (hi : i + 8 ≤ m) :
    own7 T (hist8s7 d i) (sym (a (i+2))) (sym (a (i+3))) (sym (a (i+4))) (sym (a (i+5)))
      (sym (a (i+6))) (sym (a (i+7))) = false := by
  have e2 : wforb6 T.k6 ((hist8s7 d i).drop 5) [sym (a (i+6)), sym (a (i+7))] = false :=
    hw.w2 (i+5) (by omega)
  have e3 : wforb6 T.k6 ((hist8s7 d i).drop 4) [sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] =
    false := hw.w3 (i+4) (by omega)
  have e4 : wforb6 T.k6 ((hist8s7 d i).drop 3)
      [sym (a (i+4)), sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false := hw.w4 (i+3) (by omega)
  have e5 : wforb6 T.k6 ((hist8s7 d i).drop 2)
      [sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false :=
    hw.w5 (i+2) (by omega)
  have e6 : wforb6 T.k6 ((hist8s7 d i).drop 1) [sym (a (i+2)), sym (a (i+3)), sym (a (i+4)),
      sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false := hw.w6 (i+1) (by omega)
  simp only [own7, e2, e3, e4, e5, e6, Bool.or_false]

theorem step7 (T : Tables7) (hT : StepOK7 T) (d a : Nat → Nat) (m i : Nat) (hm : i + 9 ≤ m)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : inducedPattern (win9s7 d i) = true) (hw : Windows7 T d a m) :
    T.num + Ψ7 T d a (i+1) ≤ T.den * sym (a (i+8)) + Ψ7 T d a i :=
  step7_raw T hT (win9s7 d i) rfl (a (i+2)) (a (i+3)) (a (i+4)) (a (i+5)) (a (i+6)) (a (i+7))
    (a (i+8)) (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega))
    (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega))
    (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega)) hind
    (hw.w6.w2 (i+5) (by omega)) (hw.w6.w3 (i+4) (by omega)) (hw.w6.w4 (i+3) (by omega))
    (hw.w6.w5 (i+2) (by omega)) (hw.w6.w6 (i+1) (by omega))
    (hw.w6.w2 (i+6) (by omega)) (hw.w6.w3 (i+5) (by omega)) (hw.w6.w4 (i+4) (by omega))
    (hw.w6.w5 (i+3) (by omega)) (hw.w6.w6 (i+2) (by omega)) (hw.w7 (i+1) (by omega))
    (hw.wh i hm)

/-- `S7 a n = Σ_{t<n} sym (a (t+8))`. -/
def S7 (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => S7 a n + sym (a (n+8))

theorem invariant7 (T : Tables7) (hT : StepOK7 T) (d a : Nat → Nat) (m : Nat)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + 9 ≤ m → inducedPattern (win9s7 d i) = true)
    (hw : Windows7 T d a m) :
    ∀ n, n + 8 ≤ m → T.num * n + Ψ7 T d a n ≤ T.den * S7 a n + Ψ7 T d a 0
  | 0, _ => by simp [S7]
  | n + 1, hn => by
    have ih := invariant7 T hT d a m hpos hind hw n (by omega)
    have hs := step7 T hT d a m n (by omega) hpos (hind n (by omega)) hw
    simp only [S7, Nat.mul_succ, Nat.mul_add]
    omega

theorem sumA_ge7 (a : Nat → Nat) (m : Nat) (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j) :
    ∀ n, n + 8 ≤ m → 7 + S7 a n ≤ sumA a (n + 7)
  | 0, h => by
    simp only [S7, sumA, Nat.zero_add, Nat.reduceAdd]
    have := hpos 1 (by omega) (by omega)
    have := hpos 2 (by omega) (by omega)
    have := hpos 3 (by omega) (by omega)
    have := hpos 4 (by omega) (by omega)
    have := hpos 5 (by omega) (by omega)
    have := hpos 6 (by omega) (by omega)
    have := hpos 7 (by omega) (by omega)
    omega
  | n + 1, h => by
    have ih := sumA_ge7 a m hpos n (by omega)
    have := sym_le (a (n+8))
    show 7 + (S7 a n + sym (a (n+8))) ≤ sumA a (n+7) + a (n+7+1)
    have he2 : n + 7 + 1 = n + 8 := by omega
    rw [he2]
    omega

/-- Internal counts of an `m`-edge path under the seven-centre window exclusions:
`num m + 7 den ≤ den Σ_{j=1}^{m-1} a j + 8 num + (2^bits - 1)`. -/
theorem total_bound7 (T : Tables7) (hT : StepOK7 T) (d a : Nat → Nat) (m : Nat) (hm : 8 ≤ m)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + 9 ≤ m → inducedPattern (win9s7 d i) = true)
    (hw : Windows7 T d a m) :
    T.num * m + 7 * T.den ≤ T.den * sumA a (m - 1) + 8 * T.num + (2 ^ T.bits - 1) := by
  have hinv := invariant7 T hT d a m hpos hind hw (m - 8) (by omega)
  have hsum := sumA_ge7 a m hpos (m - 8) (by omega)
  have h0 := Ψ7_le T d a 0
  have he : m - 8 + 7 = m - 1 := by omega
  rw [he] at hsum
  have hmul := Nat.mul_le_mul_left T.den hsum
  have hm8 : T.num * m = T.num * (m - 8) + 8 * T.num := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
    rw [show k + 8 - 8 = k by omega, Nat.mul_add, Nat.mul_comm T.num 8]
  rw [Nat.mul_add] at hmul
  omega

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.check7_of_shards
#print axioms Snake9.WindowAutomaton.step7_raw
#print axioms Snake9.WindowAutomaton.own7_false
#print axioms Snake9.WindowAutomaton.total_bound7
