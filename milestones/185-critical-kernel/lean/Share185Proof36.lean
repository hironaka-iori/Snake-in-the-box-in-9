import Share185Proof35
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem shareSum_cons (c : Centre) (cens : List Centre) :
    shareSum Mr S (c :: cens) = shareLocal Mr S c.v + shareSum Mr S cens := by
  simp [shareSum]


end Snake9.LocalWindow.Tags185
