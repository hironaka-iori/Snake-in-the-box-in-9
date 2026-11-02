import CoverTree

namespace Snake9.Shared89
open Snake9.Boxes88

/-- Separate table access from the unchanged geometric coverage recursion. -/
def checkCoverLookup (advance : Nat → Nat → Nat) (count : Nat) (getBox : Nat → Box) :
    Nat → List Nat → Nat → CoverTree → Bool
  | _, _, node, .accept => node == 1
  | _, pref, _, .reject i => decide (i < count) && coversPrefix (getBox i) pref
  | 0, _, _, .split _ => false
  | fuel+1, pref, node, .split children =>
      decide (children.length = 6) && (List.range 6).all fun j =>
        checkCoverLookup advance count getBox fuel (pref ++ [j+1]) (advance node (j+1))
          (children.getD j .accept)

theorem lookup_check_eq (advance : Nat → Nat → Nat) (count : Nat) (getBox : Nat → Box)
    (g : Diagram) (boxes : List Box)
    (hn : count = boxes.length)
    (hb : ∀ i, getBox i = boxes.getD i [])
    (hg : ∀ node symbol, advance node symbol = nextNode g node symbol)
    (fuel : Nat) (pref : List Nat) (node : Nat) (certificate : CoverTree) :
    checkCoverLookup advance count getBox fuel pref node certificate =
      checkCover g boxes fuel pref node certificate := by
  induction fuel generalizing pref node certificate with
  | zero => cases certificate <;> simp [checkCoverLookup, checkCover, hn, hb]
  | succ fuel ih =>
    cases certificate with
    | accept => rfl
    | reject i => simp [checkCoverLookup, checkCover, hn, hb]
    | split children =>
      simp only [checkCoverLookup, checkCover]
      apply congrArg (fun f => decide (children.length = 6) && (List.range 6).all f)
      funext j
      rw [ih, hg]

theorem lookup_cover_to_original (advance : Nat → Nat → Nat) (count : Nat) (getBox : Nat → Box)
    (g : Diagram) (boxes : List Box) (node : Nat) (certificate : CoverTree)
    (hn : count = boxes.length)
    (hb : ∀ i, getBox i = boxes.getD i [])
    (hg : ∀ n s, advance n s = nextNode g n s)
    (hc : checkCoverLookup advance count getBox 6 [] node certificate = true) :
    checkCover g boxes 6 [] node certificate = true := by
  simpa only [lookup_check_eq advance count getBox g boxes hn hb hg] using hc

#print axioms lookup_check_eq
#print axioms lookup_cover_to_original
end Snake9.Shared89
