import Share185Proof39
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem bc_total (i lo hi : Nat) :
    bc S E M X Mr tots i lo hi ≤ (tots.getD i dfltTot).lits.countP (lv (baseS S E M X Mr)) :=
  countP_blk_total _ _ _ _


end Snake9.LocalWindow.Tags185
