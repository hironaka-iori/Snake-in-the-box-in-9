import LocalWindowDirModel

/-!
# Families of window certificates: count-range widening

A certificate proves `Refuted W bounds` from the clause soundness of its UNSAT core and an LRAT
replay.  The clause checker (`LocalWindowTags.ctrOK`) only looks at the bounds of the counters that
occur in the core, so when the core of a key uses only the `alpha ≥ lo` counter of a centre (or
only `alpha ≤ hi`, or neither), the same core and the same LRAT proof certify the key with that
centre widened to `(lo, 21)` (or `(0, hi)`, or `(0, 21)`).

`refuted_narrow` turns one such widened statement into every key it contains: same window, each
of the first `wide.length` centres no wider, any further centres arbitrary.  The check
`widerB wide narrow` is a cheap Bool test, decided by the kernel per derived key.

Core Lean only; standard axioms.
-/

namespace Snake9.LocalWindow.Families

open Snake9.LocalWindow

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

end Snake9.LocalWindow.Families

#print axioms Snake9.LocalWindow.Families.refuted_narrow
#print axioms Snake9.LocalWindow.Families.refuted_key_of_wide
