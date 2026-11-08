import Share185Proof46
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem kind_nb {k : TotKind} {q : Nat} (h : isNb q k = true) : k = .nb q := by
  cases k <;> simp_all [isNb]



end Snake9.LocalWindow.Tags185
