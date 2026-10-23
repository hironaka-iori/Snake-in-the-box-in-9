import Mathlib.Tactic

namespace Snake9.FourRun
open Finset

/-- Disjoint six-position blocks each contain an entry different from four. -/
theorem density_of_no_six (a : Nat → Nat) (N : Nat)
    (h : ∀ r, r+6 ≤ N → ∃ i, i < 6 ∧ a (r+i) ≠ 4) :
    N / 6 ≤ ((range N).filter (fun j => a j ≠ 4)).card := by
  classical
  have hb : ∀ b : Fin (N/6), ∃ i : Nat, i < 6 ∧ a (6*b.val+i) ≠ 4 := by
    intro b
    apply h
    have hdiv := Nat.div_mul_le_self N 6
    have hb := b.isLt
    omega
  choose i hi ha using hb
  let f : Fin (N/6) → Nat := fun b => 6*b.val+i b
  have hf : ∀ b, f b ∈ ((range N).filter (fun j => a j ≠ 4)) := by
    intro b
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_, ha b⟩
    have hdiv := Nat.div_mul_le_self N 6
    have hb := b.isLt
    have hib := hi b
    dsimp [f]
    omega
  have hinj : Function.Injective f := by
    intro b c he
    have hb := hi b
    have hc := hi c
    have he' : 6*b.val+i b = 6*c.val+i c := he
    apply Fin.ext
    omega
  have hcard := card_le_card (s := (univ : Finset (Fin (N/6))).image f)
    (t := (range N).filter (fun j => a j ≠ 4)) (by
      intro x hx
      obtain ⟨b, _, rfl⟩ := mem_image.mp hx
      exact hf b)
  rw [card_image_of_injective _ hinj] at hcard
  simpa using hcard

#print axioms density_of_no_six
end Snake9.FourRun
