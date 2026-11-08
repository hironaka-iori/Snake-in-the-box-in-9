import Share185Proof47
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem share_arith {Mr e0 d t cn dd : Nat} (hd : 1 ≤ d) (hdd : d ≤ dd) (he : cn ≤ e0)
    (hm : t * dd ≤ Mr * cn) (hu : ¬ t ≤ Mr * e0 / d) : False := by
  apply hu
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact Nat.le_trans (Nat.mul_le_mul_left t hdd)
    (Nat.le_trans hm (Nat.mul_le_mul_left Mr he))


end Snake9.LocalWindow.Tags185
