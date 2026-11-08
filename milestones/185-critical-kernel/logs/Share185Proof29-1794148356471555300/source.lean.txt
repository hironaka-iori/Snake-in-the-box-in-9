import Share185Proof28
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sublG_sublist {α : Type} [DecidableEq α] : ∀ {l m : List α}, sublG l m = true → l.Sublist m
  | [], _, _ => List.nil_sublist _
  | _ :: _, [], h => by simp [sublG] at h
  | a :: as, b :: bs, h => by
    unfold sublG at h
    by_cases hab : a = b
    · subst hab; simp only [if_true] at h; exact (sublG_sublist h).cons₂ a
    · simp only [hab, if_false] at h; exact (sublG_sublist h).cons b


end Snake9.LocalWindow.Tags185
