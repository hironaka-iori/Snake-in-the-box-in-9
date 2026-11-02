import DirectionTables
namespace Snake9.Direction77
open Snake9.WindowAutomaton

def lookupCheck (xs : List (List Nat)) (i : Nat) : Bool :=
  xs.idxOf (xs.getD i []) == i

def mapCheck (i : Nat) : Bool :=
  (sourceIds.getD i 0 == sourceId i) && (targetIds.getD i 0 == targetId i)

theorem allBelow_add (n k : Nat) (p : Nat → Bool) :
    allBelow (n+k) p = (allBelow n p && allBelow k (fun i => p (n+i))) := by
  induction k with
  | zero => simp [allBelow]
  | succ k ih =>
    change (allBelow (n+k) p && p (n+k)) =
      (allBelow n p && (allBelow k (fun i => p (n+i)) && p (n+k)))
    rw [ih, Bool.and_assoc]

#print axioms allBelow_add
end Snake9.Direction77
