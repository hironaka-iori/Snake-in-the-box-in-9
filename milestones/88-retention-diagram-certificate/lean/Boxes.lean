import Mathlib.Tactic

namespace Snake9.Boxes88

abbrev Box := List (Nat × Nat)

def inside (b : Box) (f : Nat → Nat) : Prop :=
  ∀ j, j < 6 → (b.getD j (1,6)).1 ≤ f j ∧ f j ≤ (b.getD j (1,6)).2

def insideB (b : Box) (f : Nat → Nat) : Bool :=
  (List.range 6).all fun j => decide
    ((b.getD j (1,6)).1 ≤ f j ∧ f j ≤ (b.getD j (1,6)).2)

theorem insideB_iff (b : Box) (f : Nat → Nat) : insideB b f = true ↔ inside b f := by
  simp [insideB,inside,List.all_eq_true]

/-- A pref fixes its listed coordinates; unlisted coordinates range from one to six. -/
def coversPrefix (b : Box) (pref : List Nat) : Bool :=
  decide (pref.length ≤ 6) && (List.range 6).all fun j =>
    if j < pref.length then decide
      ((b.getD j (1,6)).1 ≤ pref.getD j 0 ∧
       pref.getD j 0 ≤ (b.getD j (1,6)).2)
    else decide ((b.getD j (1,6)).1 ≤ 1 ∧ 6 ≤ (b.getD j (1,6)).2)

theorem coversPrefix_sound (b : Box) (pref : List Nat) (f : Nat → Nat)
    (hc : coversPrefix b pref = true)
    (hprefix : ∀ j, j < pref.length → f j = pref.getD j 0)
    (hvalid : ∀ j, j < 6 → 1 ≤ f j ∧ f j ≤ 6) : inside b f := by
  have h := (Bool.and_eq_true_iff.mp hc).2
  intro j hj
  have htest := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  by_cases hp : j < pref.length
  · simp only [hp, ↓reduceIte, decide_eq_true_eq] at htest
    simpa only [hprefix j hp] using htest
  · simp only [hp, ↓reduceIte, decide_eq_true_eq] at htest
    have hv := hvalid j hj
    omega

#print axioms insideB_iff
#print axioms coversPrefix_sound
end Snake9.Boxes88
