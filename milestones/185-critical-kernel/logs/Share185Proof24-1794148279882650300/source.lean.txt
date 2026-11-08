import Share185Proof23
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem countP_blk_le (f : Nat → Bool) (l : List Nat) (lo hi : Nat) :
    (blk l lo hi).countP f ≤ hi - lo :=
  Nat.le_trans (List.countP_le_length) (List.length_take_le _ _)


end Snake9.LocalWindow.Tags185
