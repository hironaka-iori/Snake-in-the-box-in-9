import Share185Proof36
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem shareLocal_fl (x : Nat) :
    shareLocal Mr S x = ((List.range 9).map fun k => fl Mr S (x ^^^ (1 <<< k))).sum := rfl


end Snake9.LocalWindow.Tags185
