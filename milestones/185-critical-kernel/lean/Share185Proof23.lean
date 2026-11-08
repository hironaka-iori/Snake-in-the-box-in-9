import Share185Proof22
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem countP_blk_split (f : Nat → Bool) (l : List Nat) {lo mid hi : Nat} (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) :
    (blk l lo hi).countP f = (blk l lo mid).countP f + (blk l mid hi).countP f := by
  rw [blk_split l h1 h2, List.countP_append]


end Snake9.LocalWindow.Tags185
