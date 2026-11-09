import LocalWindowDirModel
import LocalWindowBridge
import LocalWindowTags

/-!
# Families of window certificates: one certificate, many keys

A certificate proves `Refuted W bounds` from the clause soundness of its UNSAT core and an LRAT
replay.  The clause checker (`LocalWindowTags.ctrOK`) only looks at the bounds of the counters that
occur in the core, so when the core of a key uses only the `alpha ≥ lo` counter of a centre (or
only `alpha ≤ hi`, or neither), the same core and the same LRAT proof certify the key with that
centre widened to `(lo, 21)` (or `(0, hi)`, or `(0, 21)`).  One such *widened* statement then
implies other keys (`milestones/30-certificate-families/README.md`):

* **L1** `refuted_narrow` / `refuted_key_of_wide`: the same window, every centre no wider.  The
  check `widerB wide narrow` is a cheap Bool test, decided by the kernel per derived key.
* **L2** `refuted_sub` / `refuted_key_sub`: a window `W'` whose image under a cube automorphism
  `φ = amap Q s` (`LocalWindowBridge`) lies in `W`, for instance a sub-window of `W`, read in
  either direction and with its directions relabelled.  Every centre of `W'` either maps to a
  centre of `W` with the same pair of path directions and a narrower count range, or carries the
  trivial range `(0, ≥ 21)` (an uncounted centre).  The check `subOK Q s W' b' W b` is a Bool
  test on the two windows and their centres, decided by the kernel per derived key; the
  generator supplies `Q` (as `mkPerm v` for a permutation list `v` of `0..8`) and `s`.

L2 rests on `axioms_pull`: the pull-back `u ↦ u < 512 ∧ S (φ u)` of a vertex set satisfying
`Axioms` for `W` satisfies `Axioms` for `W'`.  This is the generic analogue of `frame_axioms`
(which builds the axioms from a snake): degrees, cycles and endpoint conditions are invariant
under a cube automorphism (`cnt_amap`), and so are the absent-corner counts (`absent_pull`).

Both lemmas leave the statement `Refuted (winOf ds) (boundsOf syms)` of every key unchanged, so
`AllRefutedList`, the bridges and the automata are untouched.

Core Lean only; standard axioms.
-/

namespace Snake9.LocalWindow.Families

open Snake9.LocalWindow

/-! ## L1: count-range widening on the same window -/

/-- `wide` is pointwise at least as wide as `narrow` on its own length. -/
def widerB : List (Nat × Nat) → List (Nat × Nat) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | w :: ws, n :: ns => decide (w.1 ≤ n.1) && decide (n.2 ≤ w.2) && widerB ws ns

theorem widerB_spec : ∀ (wide narrow : List (Nat × Nat)), widerB wide narrow = true →
    wide.length ≤ narrow.length ∧ ∀ i, i < wide.length →
      (wide.getD i (0, 21)).1 ≤ (narrow.getD i (0, 21)).1 ∧
        (narrow.getD i (0, 21)).2 ≤ (wide.getD i (0, 21)).2
  | [], _, _ => ⟨Nat.zero_le _, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | _ :: _, [], h => by simp [widerB] at h
  | w :: ws, n :: ns, h => by
    simp only [widerB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨hl, hi⟩ := widerB_spec ws ns h3
    refine ⟨by simp only [List.length_cons]; omega, ?_⟩
    intro i hi'
    cases i with
    | zero => exact ⟨h1, h2⟩
    | succ i =>
      simp only [List.getD_cons_succ]
      exact hi i (by simp only [List.length_cons] at hi'; omega)

/-- A refutation with wider count ranges refutes every narrower key on the same window. -/
theorem refuted_narrow {W : List Nat} {wide narrow : List (Nat × Nat)}
    (h : Refuted W wide) (hw : widerB wide narrow = true) : Refuted W narrow := by
  obtain ⟨hl, hb⟩ := widerB_spec wide narrow hw
  intro S E hax
  apply h S E
  refine { hax with alpha := ?_ }
  intro c hc
  simp only [centresOf, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  have hmem : Centre.mk (W.getD (i + 1) 0) (dirOfStep (W.getD i 0) (W.getD (i + 1) 0))
      (dirOfStep (W.getD (i + 1) 0) (W.getD (i + 2) 0))
      (narrow.getD i (0, 21)).1 (narrow.getD i (0, 21)).2 ∈
        centresOf W narrow := by
    simp only [centresOf, List.mem_map, List.mem_range]
    exact ⟨i, by omega, rfl⟩
  have hn := hax.alpha _ hmem
  obtain ⟨b1, b2⟩ := hb i hi
  simp only at hn ⊢
  omega

/-- The key form: a widened refutation of `winOf ds` gives the lumped key `(ds, syms)`. -/
theorem refuted_key_of_wide {ds syms : List Nat} {wide : List (Nat × Nat)}
    (h : Refuted (winOf ds) wide) (hw : widerB wide (boundsOf syms) = true) :
    Refuted (winOf ds) (boundsOf syms) :=
  refuted_narrow h hw

/-- Example: one widened statement (centre 2 uncounted) yields all six keys `[4, s, 5, 2, 4]`. -/
example {ds : List Nat} (h : Refuted (winOf ds) [(4, 4), (0, 21), (5, 5), (2, 2), (4, 4)]) :
    ∀ s, s < 7 → Refuted (winOf ds) (boundsOf [4, s, 5, 2, 4]) := by
  intro s hs
  apply refuted_key_of_wide h
  have : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Cube automorphisms and their inverses -/

theorem lt512_xor {u w : Nat} (hu : u < 512) (hw : w < 512) : u ^^^ w < 512 := by
  have h512 : (512 : Nat) = 2 ^ 9 := by decide
  rw [h512] at *
  exact Nat.xor_lt_two_pow hu hw

theorem bperm_inv_bperm (Q : CPerm) {x : Nat} (hx : x < 512) : bperm Q.inv (bperm Q x) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bperm, testBit_bperm]
  by_cases hi : i < 9
  · simp [hi, CPerm.inv, Q.fwd_lt i hi, Q.bwd_fwd i hi]
  · simp [hi, testBit_of_lt_512 hx hi]

theorem bperm_bperm_inv (Q : CPerm) {y : Nat} (hy : y < 512) : bperm Q (bperm Q.inv y) = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bperm, testBit_bperm]
  by_cases hi : i < 9
  · simp [hi, CPerm.inv, Q.bwd_lt i hi, Q.fwd_bwd i hi]
  · simp [hi, testBit_of_lt_512 hy hi]

section Auto
variable (Q : CPerm) (s : Nat)

/-- `amap Q.inv (bperm Q s)` inverts `amap Q s` on the cube. -/
theorem amap_ainv {v : Nat} (hv : v < 512) :
    amap Q s (amap Q.inv (bperm Q s) v) = v := by
  unfold amap
  rw [bperm_xor, bperm_bperm_inv Q (lt512_xor hv (bperm_lt Q s)), Nat.xor_assoc, Nat.xor_self,
    Nat.xor_zero]

theorem ainv_amap {u : Nat} (hu : u < 512) :
    amap Q.inv (bperm Q s) (amap Q s u) = u := by
  unfold amap
  rw [← bperm_xor, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, bperm_inv_bperm Q hu]

theorem nbrs_lt {u w : Nat} (hu : u < 512) (hw : w ∈ nbrs u) : w < 512 := by
  obtain ⟨k, hk, rfl⟩ := (mem_nbrs _ _).1 hw
  exact xor_pow_lt hu hk

/-- Neighbour counts are invariant under the automorphism. -/
theorem cnt_amap (hs : s < 512) (T : Nat → Bool) {u : Nat} (hu : u < 512) :
    cnt (fun x => T (amap Q s x)) (nbrs u) = cnt T (nbrs (amap Q s u)) := by
  unfold cnt
  apply Nat.le_antisymm
  · apply filter_length_le _ (nbrs_nodup u) _ (amap Q s)
      (fun x hx y hy h => amap_inj Q hs (nbrs_lt hu hx) (nbrs_lt hu hy) h)
    intro x hx hT
    obtain ⟨k, hk, rfl⟩ := (mem_nbrs _ _).1 hx
    refine ⟨?_, hT⟩
    rw [mem_nbrs, amap_flip Q s u hk]
    exact ⟨_, Q.fwd_lt k hk, rfl⟩
  · have hu' := amap_lt Q s u
    apply filter_length_le _ (nbrs_nodup _) _ (amap Q.inv (bperm Q s))
      (fun x hx y hy h => amap_inj Q.inv (bperm_lt Q s) (nbrs_lt hu' hx) (nbrs_lt hu' hy) h)
    intro x hx hT
    refine ⟨?_, by rw [amap_ainv Q s (nbrs_lt hu' hx)]; exact hT⟩
    obtain ⟨k, hk, rfl⟩ := (mem_nbrs _ _).1 hx
    rw [mem_nbrs, amap_flip Q.inv _ _ hk, ainv_amap Q s hu]
    exact ⟨_, Q.inv.fwd_lt k hk, rfl⟩

/-- The pull-back of a vertex set along `amap Q s`, restricted to the cube. -/
def pull (S : Nat → Bool) (u : Nat) : Bool := decide (u < 512) && S (amap Q s u)

theorem pull_eq {S : Nat → Bool} {u : Nat} (hu : u < 512) : pull Q s S u = S (amap Q s u) := by
  simp [pull, hu]

theorem pull_true {S : Nat → Bool} {u : Nat} (h : pull Q s S u = true) :
    u < 512 ∧ S (amap Q s u) = true := by
  simpa [pull] using h

theorem cnt_pull (hs : s < 512) (S : Nat → Bool) {u : Nat} (hu : u < 512) :
    cnt (pull Q s S) (nbrs u) = cnt S (nbrs (amap Q s u)) := by
  rw [← cnt_amap Q s hs S hu]
  unfold cnt
  rw [List.filter_congr (fun x hx => pull_eq Q s (nbrs_lt hu hx))]

end Auto

/-! ## Absent corners under a coordinate permutation -/

theorem freePairs_comm (d₁ d₂ : Nat) : freePairs d₁ d₂ = freePairs d₂ d₁ := by
  unfold freePairs
  congr 1
  funext a
  congr 1
  funext b
  by_cases h : a < b ∧ a ≠ d₁ ∧ a ≠ d₂ ∧ b ≠ d₁ ∧ b ≠ d₂
  · rw [if_pos h, if_pos ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.2.1, h'.2.1, h'.2.2.2.2, h'.2.2.2.1⟩)]

theorem absentCorners_comm (S : Nat → Bool) (c d₁ d₂ : Nat) :
    absentCorners S c d₁ d₂ = absentCorners S c d₂ d₁ := by
  unfold absentCorners
  rw [freePairs_comm]

theorem freePairs_length21 : ∀ a, a < 9 → ∀ b, b < 9 → a ≠ b → (freePairs a b).length = 21 := by
  decide

theorem absentCorners_le21 (S : Nat → Bool) (c : Nat) {d₁ d₂ : Nat} (h1 : d₁ < 9) (h2 : d₂ < 9)
    (hne : d₁ ≠ d₂) : absentCorners S c d₁ d₂ ≤ 21 := by
  unfold absentCorners
  rw [← freePairs_length21 d₁ h1 d₂ h2 hne]
  exact List.length_filter_le _ _

/-- Sorting a permuted pair. -/
def sortP (R : CPerm) (ab : Nat × Nat) : Nat × Nat :=
  (min (R.fwd ab.1) (R.fwd ab.2), max (R.fwd ab.1) (R.fwd ab.2))

theorem mem_freePairs99 {a b d₁ d₂ : Nat} (h : (a, b) ∈ freePairs d₁ d₂) : (a, b) ∈ freePairs 9 9 := by
  rw [mem_freePairs] at h ⊢
  omega

/-- One direction of the invariance of absent-corner counts, for any coordinate permutation `R`
and any two vertex sets that agree on the corners. -/
theorem absent_le (R : CPerm) (T T' : Nat → Bool) (c c' : Nat) {d₁ d₂ : Nat} (h1 : d₁ < 9)
    (h2 : d₂ < 9)
    (hT : ∀ a b, a < 9 → b < 9 → a ≠ b →
      T (c ^^^ 2 ^ a ^^^ 2 ^ b) = T' (c' ^^^ 2 ^ (R.fwd a) ^^^ 2 ^ (R.fwd b))) :
    absentCorners T c d₁ d₂ ≤ absentCorners T' c' (R.fwd d₁) (R.fwd d₂) := by
  unfold absentCorners
  apply filter_length_le _ (freePairs_nodup d₁ (by omega) d₂ (by omega)) _ (sortP R)
    (fun x hx y hy h => sorted_mem_inj R x (mem_freePairs99 hx) y (mem_freePairs99 hy) h)
  rintro ⟨a, b⟩ hx hs
  rw [mem_freePairs] at hx
  obtain ⟨hab, hb9, ha1, ha2, hb1, hb2⟩ := hx
  have ha9 : a < 9 := by omega
  have hne : R.fwd a ≠ R.fwd b := fun e => by have := R.fwd_inj ha9 hb9 e; omega
  have n1 : ∀ x, x < 9 → x ≠ d₁ → R.fwd x ≠ R.fwd d₁ := fun x hx hn e => hn (R.fwd_inj hx h1 e)
  have n2 : ∀ x, x < 9 → x ≠ d₂ → R.fwd x ≠ R.fwd d₂ := fun x hx hn e => hn (R.fwd_inj hx h2 e)
  have fa := R.fwd_lt a ha9
  have fb := R.fwd_lt b hb9
  have e1 := n1 a ha9 ha1
  have e2 := n2 a ha9 ha2
  have e3 := n1 b hb9 hb1
  have e4 := n2 b hb9 hb2
  simp only [Nat.one_shiftLeft] at hs ⊢
  rw [hT a b ha9 hb9 (by omega)] at hs
  unfold sortP
  simp only
  by_cases hle : R.fwd a ≤ R.fwd b
  · rw [Nat.min_eq_left hle, Nat.max_eq_right hle]
    exact ⟨(mem_freePairs _ _ _ _).2 ⟨by omega, fb, e1, e2, e3, e4⟩, hs⟩
  · rw [Nat.min_eq_right (by omega), Nat.max_eq_left (by omega)]
    refine ⟨(mem_freePairs _ _ _ _).2 ⟨by omega, fa, e3, e4, e1, e2⟩, ?_⟩
    rw [Nat.xor_assoc, Nat.xor_comm (2 ^ R.fwd b), ← Nat.xor_assoc]
    exact hs

theorem corner_lt {c a b : Nat} (hc : c < 512) (ha : a < 9) (hb : b < 9) :
    c ^^^ 2 ^ a ^^^ 2 ^ b < 512 :=
  xor_pow_lt (xor_pow_lt hc ha) hb

/-- Absent-corner counts are invariant under the automorphism. -/
theorem absent_pull (Q : CPerm) (s : Nat) (S : Nat → Bool) {c d₁ d₂ : Nat}
    (hc : c < 512) (h1 : d₁ < 9) (h2 : d₂ < 9) :
    absentCorners (pull Q s S) c d₁ d₂ = absentCorners S (amap Q s c) (Q.fwd d₁) (Q.fwd d₂) := by
  apply Nat.le_antisymm
  · apply absent_le Q _ _ c _ h1 h2
    intro a b ha hb _
    rw [pull_eq Q s (corner_lt hc ha hb), amap_flip Q s _ hb, amap_flip Q s _ ha]
  · have h := absent_le Q.inv S (pull Q s S) (amap Q s c) c (Q.fwd_lt d₁ h1) (Q.fwd_lt d₂ h2)
      (fun a b ha hb _ => by
        have ha' : Q.bwd a < 9 := Q.bwd_lt a ha
        have hb' : Q.bwd b < 9 := Q.bwd_lt b hb
        show S (amap Q s c ^^^ 2 ^ a ^^^ 2 ^ b) = pull Q s S (c ^^^ 2 ^ Q.bwd a ^^^ 2 ^ Q.bwd b)
        rw [pull_eq Q s (corner_lt hc ha' hb'), amap_flip Q s _ hb', amap_flip Q s _ ha',
          Q.fwd_bwd a ha, Q.fwd_bwd b hb])
    simpa only [CPerm.inv, Q.bwd_fwd d₁ h1, Q.bwd_fwd d₂ h2] using h

/-! ## The axioms under an automorphism -/

/-- If `Axioms S E W cen` holds and the automorphism `φ = amap Q s` sends the window `W'` into
`W` and every centre of `cen'` onto a centre of `cen` with the same path directions and a
narrower count range (or the centre of `cen'` has the trivial range), then the pull-backs of
`S` and `E` satisfy `Axioms` for `W'` and `cen'`. -/
theorem axioms_pull (Q : CPerm) (s : Nat) (hs : s < 512) {S E : Nat → Bool} {W W' : List Nat}
    {cen cen' : List Centre} (hax : Axioms S E W cen)
    (hwin : ∀ v ∈ W', v < 512 ∧ amap Q s v ∈ W)
    (hcen : ∀ c' ∈ cen', c'.v < 512 ∧ c'.d₁ < 9 ∧ c'.d₂ < 9 ∧
      ((∃ c ∈ cen, c.v = amap Q s c'.v ∧
          ((c.d₁ = Q.fwd c'.d₁ ∧ c.d₂ = Q.fwd c'.d₂) ∨ (c.d₁ = Q.fwd c'.d₂ ∧ c.d₂ = Q.fwd c'.d₁)) ∧
          c'.lo ≤ c.lo ∧ c.hi ≤ c'.hi) ∨
        (c'.lo = 0 ∧ 21 ≤ c'.hi ∧ c'.d₁ ≠ c'.d₂))) :
    Axioms (pull Q s S) (pull Q s E) W' cen' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- window_sel
    intro v hv
    obtain ⟨hv5, hvW⟩ := hwin v hv
    rw [pull_eq Q s hv5]
    exact hax.window_sel _ hvW
  · -- sel_lt
    intro v hv
    exact (pull_true Q s hv).1
  · -- deg_le_two
    intro v hv
    obtain ⟨hv5, hSv⟩ := pull_true Q s hv
    rw [cnt_pull Q s hs S hv5]
    exact hax.deg_le_two _ hSv
  · -- deg_pos
    intro v hv
    obtain ⟨hv5, hSv⟩ := pull_true Q s hv
    rw [cnt_pull Q s hs S hv5]
    exact hax.deg_pos _ hSv
  · -- acyclic
    intro C hne hdeg
    by_cases hbig : ∃ v ∈ C, ¬ v < 512
    · obtain ⟨v, hv, hv5⟩ := hbig
      exact ⟨v, hv, by simp [pull, hv5]⟩
    have hlt : ∀ v ∈ C, v < 512 := fun v hv => Classical.byContradiction fun h => hbig ⟨v, hv, h⟩
    have hcont : ∀ x, x < 512 → (C.map (amap Q s)).contains (amap Q s x) = C.contains x := by
      intro x hx
      apply Bool.eq_iff_iff.2
      rw [List.contains_iff, List.contains_iff, List.mem_map]
      constructor
      · rintro ⟨y, hy, he⟩
        rw [← amap_inj Q hs (hlt y hy) hx he]
        exact hy
      · intro h
        exact ⟨x, h, rfl⟩
    obtain ⟨w, hw, hSw⟩ := hax.acyclic (C.map (amap Q s))
      (by intro h; exact hne (List.map_eq_nil_iff.1 h)) (by
        intro w hw
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
        rw [← cnt_amap Q s hs _ (hlt v hv)]
        unfold cnt
        rw [List.filter_congr (fun x hx => hcont x (nbrs_lt (hlt v hv) hx))]
        exact hdeg v hv)
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    exact ⟨v, hv, by rw [pull_eq Q s (hlt v hv)]; exact hSw⟩
  · -- end_sel
    intro v hv
    obtain ⟨hv5, hEv⟩ := pull_true Q s hv
    rw [pull_eq Q s hv5]
    exact hax.end_sel _ hEv
  · -- low_end
    intro v hv hc1
    obtain ⟨hv5, hSv⟩ := pull_true Q s hv
    rw [cnt_pull Q s hs S hv5] at hc1
    rw [pull_eq Q s hv5]
    exact hax.low_end _ hSv hc1
  · -- end_low
    intro v hv
    obtain ⟨hv5, hEv⟩ := pull_true Q s hv
    rw [cnt_pull Q s hs S hv5]
    exact hax.end_low _ hEv
  · -- end_two
    intro a b c ha hb hc
    obtain ⟨ha5, ha'⟩ := pull_true Q s ha
    obtain ⟨hb5, hb'⟩ := pull_true Q s hb
    obtain ⟨hc5, hc'⟩ := pull_true Q s hc
    rcases hax.end_two _ _ _ ha' hb' hc' with h | h | h
    · exact Or.inl (amap_inj Q hs ha5 hb5 h)
    · exact Or.inr (Or.inl (amap_inj Q hs ha5 hc5 h))
    · exact Or.inr (Or.inr (amap_inj Q hs hb5 hc5 h))
  · -- alpha
    intro c' hc'
    obtain ⟨hv5, h1, h2, hcase⟩ := hcen c' hc'
    rcases hcase with ⟨c, hc, hcv, hd, hlo, hhi⟩ | ⟨hlo, hhi, hne⟩
    · rw [absent_pull Q s S hv5 h1 h2]
      have ha := hax.alpha c hc
      rcases hd with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [hcv, e1, e2] at ha
        omega
      · rw [hcv, e1, e2, absentCorners_comm] at ha
        omega
    · have := absentCorners_le21 (pull Q s S) c'.v h1 h2 hne
      omega

/-! ## L2: sub-windows, reversal and relabelling -/

/-- The Bool check of `refuted_sub`: `amap Q s` sends every vertex of `W'` into `W`, and every
centre of `W'` (bounds `b'`) onto a centre of `W` (bounds `b`) with the same path directions and a
narrower range, unless its range is trivial.  Centres are those of `Tags.centresK`, which the
kernel evaluates. -/
def subOK (Q : CPerm) (s : Nat) (W' : List Nat) (b' : List (Nat × Nat)) (W : List Nat)
    (b : List (Nat × Nat)) : Bool :=
  decide (s < 512) &&
  W'.all (fun v => decide (v < 512) && W.contains (amap Q s v)) &&
  (Tags.centresK W' b').all (fun c' =>
    decide (c'.v < 512) && decide (c'.d₁ < 9) && decide (c'.d₂ < 9) &&
    ((Tags.centresK W b).any (fun c =>
        decide (c.v = amap Q s c'.v) &&
        ((decide (c.d₁ = Q.fwd c'.d₁) && decide (c.d₂ = Q.fwd c'.d₂)) ||
          (decide (c.d₁ = Q.fwd c'.d₂) && decide (c.d₂ = Q.fwd c'.d₁))) &&
        decide (c'.lo ≤ c.lo) && decide (c.hi ≤ c'.hi)) ||
      (decide (c'.lo = 0) && decide (21 ≤ c'.hi) && decide (c'.d₁ ≠ c'.d₂))))

/-- **L2.** A refutation of `W'` with bounds `b'` refutes `W` with bounds `b` whenever `subOK`
accepts an automorphism `amap Q s` from `W'` into `W`. -/
theorem refuted_sub {W W' : List Nat} {b b' : List (Nat × Nat)} (Q : CPerm) (s : Nat)
    (h : Refuted W' b') (hok : subOK Q s W' b' W b = true) : Refuted W b := by
  intro S E hax
  simp only [subOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨hs, hw⟩, hc⟩ := hok
  rw [Tags.centresK_eq] at hax
  apply h (pull Q s S) (pull Q s E)
  rw [Tags.centresK_eq]
  refine axioms_pull Q s hs hax (fun v hv => ?_) (fun c' hc' => ?_)
  · have := hw v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff] at this
    exact this
  · have := hc c' hc'
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at this
    obtain ⟨⟨⟨hv, h1⟩, h2⟩, hcase⟩ := this
    refine ⟨hv, h1, h2, ?_⟩
    rcases hcase with ⟨c, hc, ⟨⟨hcv, hd⟩, hlo⟩, hhi⟩ | ⟨⟨hlo, hhi⟩, hne⟩
    · exact Or.inl ⟨c, hc, hcv, hd, hlo, hhi⟩
    · exact Or.inr ⟨hlo, hhi, hne⟩

/-- The key form: a widened refutation of a window `winOf cs` gives the lumped key `(ds, syms)`
when `amap Q s` maps `winOf cs` into `winOf ds` (`subOK`). -/
theorem refuted_key_sub {cs ds syms : List Nat} {wide : List (Nat × Nat)} (Q : CPerm) (s : Nat)
    (h : Refuted (winOf cs) wide) (hok : subOK Q s (winOf cs) wide (winOf ds) (boundsOf syms) = true) :
    Refuted (winOf ds) (boundsOf syms) :=
  refuted_sub Q s h hok

/-- Example: the window `0,1,2` read backwards from the last vertex `6` of `winOf [0, 1, 2, 0]`
(directions `0, 2, 1` there, relabelled by the transposition of `1` and `2`): a refutation of
`([0, 1, 2], [(3, 3), (0, 21)])` gives every key `([0, 1, 2, 0], [a, b, 3])`. -/
example (h : Refuted (winOf [0, 1, 2]) [(3, 3), (0, 21)]) :
    Refuted (winOf [0, 1, 2, 0]) (boundsOf [5, 6, 3]) :=
  refuted_key_sub (mkPerm [0, 2, 1, 3, 4, 5, 6, 7, 8]) 6 h (by decide +kernel)

end Snake9.LocalWindow.Families

#print axioms Snake9.LocalWindow.Families.refuted_narrow
#print axioms Snake9.LocalWindow.Families.refuted_key_of_wide
#print axioms Snake9.LocalWindow.Families.axioms_pull
#print axioms Snake9.LocalWindow.Families.refuted_sub
#print axioms Snake9.LocalWindow.Families.refuted_key_sub
