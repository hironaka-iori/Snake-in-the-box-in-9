import Share185Proof53
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem refutedShare_of_sat {window : List Nat} {bounds : List (Nat × Nat)} {Mr cap : Nat}
    {f : List (List Int)}
    (hsat : ∀ S E : Nat → Bool, AxiomsS S E window (centresOf window bounds) Mr cap →
      ∃ τ, cnfTrue τ f = true)
    (hunsat : Unsat f) : RefutedShare window bounds Mr cap := by
  intro S E ax
  obtain ⟨τ, hτ⟩ := hsat S E ax
  rw [hunsat τ] at hτ
  exact Bool.false_ne_true hτ



end Snake9.LocalWindow.Tags185
