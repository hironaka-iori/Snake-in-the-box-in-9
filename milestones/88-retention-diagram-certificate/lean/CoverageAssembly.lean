import BoxWitness
import CoverTree

namespace Snake9.Boxes88
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.History78 Snake9.GraphWalk78
open Snake9.Guards79 Snake9.Retained87

def entriesValid (q di : Nat) (entries : List (Box × Witness)) : Bool :=
  entries.all fun item => boxWitnessValid q di item.1 item.2

theorem digits_getD (code j : Nat) (hj : j < 6) :
    (digits code).getD j 0 = digit code j := by
  interval_cases j <;> rfl

theorem entries_avoided (q di code : Nat) (entries : List (Box × Witness))
    (hc : code < 46656) (hv : entriesValid q di entries = true)
    (hkeep : numericKeep q di code = true) :
    ∀ b ∈ entries.map Prod.fst, ¬inside b (digit code) := by
  intro b hb
  obtain ⟨item,hm,heq⟩ := List.mem_map.mp hb
  subst b
  exact boxWitnessValid_sound q di code item.1 item.2 hc
    (List.all_eq_true.mp hv item hm) hkeep

/-- Checked rejection witnesses and a checked cover imply diagram membership.
Both finite checks are explicit premises. -/
theorem numeric_keep_implies_diagram (q di code : Nat) (g : Diagram) (node : Nat)
    (entries : List (Box × Witness)) (certificate : CoverTree)
    (hc : code < 46656) (hv : entriesValid q di entries = true)
    (hcover : checkCover g (entries.map Prod.fst) 6 [] node certificate = true)
    (hkeep : numericKeep q di code = true) :
    diagramEval g node (digits code) = true := by
  apply cover_implies_membership g (entries.map Prod.fst) node certificate hcover
    (digits code) (by simp [digits])
  · intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    exact digit_range code j
  · intro b hb hin
    apply entries_avoided q di code entries hc hv hkeep b hb
    intro j hj
    simpa only [digits_getD code j hj] using hin j hj

/-- Actual snakes enter the diagram under the two inherited catalogue premises
and the concrete witness-validity and coverage checks for their state. -/
theorem actual_snake_implies_diagram (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m)
    (g : Diagram) (node : Nat) (entries : List (Box × Witness)) (certificate : CoverTree)
    (hv : entriesValid (actualHistory p r) (directionId p r) entries = true)
    (hcover : checkCover g (entries.map Prod.fst) 6 [] node certificate = true) :
    diagramEval g node (digits (sixCode p r)) = true := by
  exact numeric_keep_implies_diagram (actualHistory p r) (directionId p r) (sixCode p r)
    g node entries certificate (actual_range_compatible p r hr).1.2.2 hv hcover
    (actual_numeric_keep h235 h236 p r hr)

#print axioms digits_getD
#print axioms entries_avoided
#print axioms numeric_keep_implies_diagram
#print axioms actual_snake_implies_diagram
end Snake9.Boxes88
