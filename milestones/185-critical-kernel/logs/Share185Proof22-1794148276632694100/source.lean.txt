import Share185Proof21
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem blk_split (l : List Nat) {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    blk l lo hi = blk l lo mid ++ blk l mid hi := by
  unfold blk
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega, List.take_add, List.drop_drop,
    show lo + (mid - lo) = mid by omega]


end Snake9.LocalWindow.Tags185
