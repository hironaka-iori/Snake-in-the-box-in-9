import Share185Proof54
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem refutedShare_of_check {window : List Nat} {bounds : List (Nat × Nat)} {Mr cap : Nat}
    (M : MT) (X : MS) (cs : List Ctr) (tots : List Tot) (tags : List TagS)
    (raw : List (List Nat))
    (h : checkAllS M X Mr cs tots window bounds cap tags raw = true)
    (hunsat : Unsat (raw.map (·.map decodeLit))) : RefutedShare window bounds Mr cap :=
  refutedShare_of_sat (fun S E ax => ⟨_, soundS M X Mr cs tots window bounds cap tags raw h S E ax⟩)
    hunsat


end Snake9.LocalWindow.Tags185
