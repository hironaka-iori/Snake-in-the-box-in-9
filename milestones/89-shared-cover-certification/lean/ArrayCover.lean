import CoverTree

namespace Snake9.Shared89
open Snake9.Boxes88

/-- The same coverage equation with direct array lookup for box indices. -/
def checkCoverArray (g : Diagram) (boxes : Array Box) :
    Nat → List Nat → Nat → CoverTree → Bool
  | _, _, node, .accept => node == 1
  | _, pref, _, .reject i => decide (i < boxes.size) && coversPrefix (boxes.getD i []) pref
  | 0, _, _, .split _ => false
  | fuel+1, pref, node, .split children =>
      decide (children.length = 6) && (List.range 6).all fun j =>
        checkCoverArray g boxes fuel (pref ++ [j+1]) (nextNode g node (j+1))
          (children.getD j .accept)

theorem array_check_eq (g : Diagram) (boxes : Array Box) (fuel : Nat)
    (pref : List Nat) (node : Nat) (certificate : CoverTree) :
    checkCoverArray g boxes fuel pref node certificate =
      checkCover g boxes.toList fuel pref node certificate := by
  induction fuel generalizing pref node certificate with
  | zero =>
    cases certificate <;>
      simp [checkCoverArray, checkCover, Array.getD_eq_getD_getElem?,
        List.getD_eq_getElem?_getD]
  | succ fuel ih =>
    cases certificate with
    | accept => rfl
    | reject i =>
      simp [checkCoverArray, checkCover, Array.getD_eq_getD_getElem?,
        List.getD_eq_getElem?_getD]
    | split children =>
      simp only [checkCoverArray, checkCover]
      exact congrArg (fun f => decide (children.length = 6) && (List.range 6).all f)
        (funext fun j => ih (pref ++ [j+1]) (nextNode g node (j+1))
          (children.getD j .accept))

theorem array_cover_to_list (g : Diagram) (boxes : List Box) (node : Nat)
    (certificate : CoverTree)
    (hc : checkCoverArray g boxes.toArray 6 [] node certificate = true) :
    checkCover g boxes 6 [] node certificate = true := by
  simpa only [array_check_eq, List.toList_toArray] using hc

#print axioms array_check_eq
#print axioms array_cover_to_list
end Snake9.Shared89
