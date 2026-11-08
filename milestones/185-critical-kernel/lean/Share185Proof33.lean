import Share185Proof32
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sum_sublist_le : ∀ {l₁ l₂ : List Nat}, l₁.Sublist l₂ → l₁.sum ≤ l₂.sum
  | _, _, .slnil => Nat.le_refl _
  | _, _, .cons a h => by rw [List.sum_cons]; have := sum_sublist_le h; omega
  | _, _, .cons₂ a h => by rw [List.sum_cons, List.sum_cons]; have := sum_sublist_le h; omega


end Snake9.LocalWindow.Tags185
