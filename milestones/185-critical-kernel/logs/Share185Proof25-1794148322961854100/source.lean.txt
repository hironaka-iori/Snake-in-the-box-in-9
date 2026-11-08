import Share185Proof24
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem countP_blk_total (f : Nat → Bool) (l : List Nat) (lo hi : Nat) :
    (blk l lo hi).countP f ≤ l.countP f :=
  ((List.take_sublist _ _).trans (List.drop_sublist _ _)).countP_le


end Snake9.LocalWindow.Tags185
