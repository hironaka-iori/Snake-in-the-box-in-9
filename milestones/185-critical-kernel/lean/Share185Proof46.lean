import Share185Proof45
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem kind_emp {k : TotKind} {q : Nat} (h : isEmp q k = true) : k = .emp q := by
  cases k <;> simp_all [isEmp]


end Snake9.LocalWindow.Tags185
