import CombinedEnvironment98

/-!
Actual defined-graph walks with the full saved row key retained.
Each step uses one common in-bounds index for its row and both endpoints.
The two reference-catalogue refutation premises remain explicit.
-/
namespace Snake9.ActualGraphKeys98
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.History78 Snake9.GraphWalk78
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Batch92
open Snake9.Enumeration87 Snake9.Assembly87 Snake9.DefinedGraph92

set_option maxHeartbeats 2000000

/-- One actual step has a common saved index carrying its entire key and
both endpoint identities. No endpoint-based edge identification is used. -/
theorem defined_actual_edge_key (g : Diagram)
    (hfamily : ClassMembershipFamily g) (hcheck : assignmentCheck = true)
    (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    ∃ edge : Fin (rows g).size,
      (rows g).toList[edge.val]? =
        some (directionId p r, actualHistory p r, sixCode p r) ∧
      (sources g).toList[edge.val]? = some (actualState p r) ∧
      (targets g).toList[edge.val]? = some (actualState p (r+1)) := by
  obtain ⟨i, hi⟩ := actual_saved_edge h235 h236
    (rows g) (sources g) (targets g)
    (defined_graph_covers g hfamily hcheck)
    (defined_endpoint_columns g).1 (defined_endpoint_columns g).2 p r hr
  have hibound : i < (rows g).size := by
    have h := (List.getElem?_eq_some_iff.mp hi.1).choose
    simpa using h
  exact ⟨⟨i, hibound⟩, hi⟩

/-- The full key and the endpoints use the same edge function at every
actual step. The statement also covers the empty step range when m≤8. -/
theorem defined_actual_key_walk (g : Diagram)
    (hfamily : ClassMembershipFamily g) (hcheck : assignmentCheck = true)
    (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    {m : Nat} (p : Snake m) :
    ∃ edge : Fin (m-8) → Fin (rows g).size, ∀ i,
      (rows g).toList[(edge i).val]? =
        some (directionId p i.val, actualHistory p i.val, sixCode p i.val) ∧
      (sources g).toList[(edge i).val]? = some (actualState p i.val) ∧
      (targets g).toList[(edge i).val]? = some (actualState p (i.val+1)) := by
  classical
  have step (i : Fin (m-8)) := defined_actual_edge_key g hfamily hcheck
    h235 h236 p i.val (by have h := i.isLt; omega)
  choose edge hedge using step
  exact ⟨edge, hedge⟩

/-- The saved retained diagram supplies the checked class family and
assignment certificate. Only the two reference catalogues remain premises. -/
theorem retained_actual_key_walk
    (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    {m : Nat} (p : Snake m) :
    ∃ edge : Fin (m-8) → Fin (rows retainedDiagram).size, ∀ i,
      (rows retainedDiagram).toList[(edge i).val]? =
        some (directionId p i.val, actualHistory p i.val, sixCode p i.val) ∧
      (sources retainedDiagram).toList[(edge i).val]? =
        some (actualState p i.val) ∧
      (targets retainedDiagram).toList[(edge i).val]? =
        some (actualState p (i.val+1)) :=
  defined_actual_key_walk retainedDiagram retained_class_family assignment_checked
    h235 h236 p

#print axioms defined_actual_edge_key
#print axioms defined_actual_key_walk
#print axioms retained_actual_key_walk
end Snake9.ActualGraphKeys98
