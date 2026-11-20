import NatPack
/-! Split a flat list at zeros, kernel-friendly (`List.rec`, no `reverse`): the packed form of a
clause list.  Literals are coded ≥ 2, `0` ends a clause; each clause is stored with its literals in
reverse order, so accumulating with `cons` restores the original order. -/
namespace Snake9.SplitZ

noncomputable section

local macro "kif " c:term " then " t:term " else " e:term : term =>
  `(Bool.rec (motive := fun _ => _) $e $t $c)

def splitZ (l : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List Nat → List (List Nat)) (fun _ => [])
    (fun x _ ih acc => kif Nat.beq x 0 then List.cons acc (ih []) else ih (List.cons x acc)) l []

end

end Snake9.SplitZ
