import ContextAssignment
import ArrayAssembly

namespace Snake9.DefinedGraph92
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.History78 Snake9.GraphWalk78
open Snake9.Boxes88 Snake9.Batch92 Snake9.Retained87 Snake9.Enumeration87
open Snake9.Assembly87

/-- Missing blocks reject. Assigned blocks use their recorded class root. -/
def diagramKeep (g : Diagram) (di q code : Nat) : Bool :=
  match savedBlockClass (75*di+q) with
  | none => false
  | some cls => diagramEval g (recordedClassRoot cls) (digits code)

/-- This is a defined proof graph, with no equality to an external row file assumed. -/
def rows (g : Diagram) : Array Row := (generatedRows (diagramKeep g)).toArray

def sources (g : Diagram) : Array Nat := ((rows g).toList.map rowSource).toArray
def targets (g : Diagram) : Array Nat := ((rows g).toList.map rowTarget).toArray

theorem defined_graph_covers (g : Diagram)
    (hfamily : ClassMembershipFamily g) (hcheck : assignmentCheck = true) :
    RetentionCover retainedKeep (rows g).toList := by
  intro di q code hd hq hc hk
  obtain ⟨ha,he⟩ := numeric_membership_of_assignment g hfamily hcheck q di code hd hk
  have hb : savedBlockClass (75*di+q) = some (chosenClass di q) := ha.2.2.1
  have accepted : diagramKeep g di q code = true := by
    simpa only [diagramKeep,hb] using he
  have hm := (generated_row_iff (diagramKeep g) di q code).mpr ⟨hd,hq,hc,accepted⟩
  simpa only [rows, List.toList_toArray] using hm

theorem defined_endpoint_columns (g : Diagram) :
    (sources g).toList = (rows g).toList.map rowSource ∧
    (targets g).toList = (rows g).toList.map rowTarget := by
  simp only [sources,targets,List.toList_toArray,and_self]

/-- Weight and potential certificates must be checked on these defined rows.
The family, finite assignment and both reference catalogues remain premises. -/
theorem defined_actual_walk (g : Diagram)
    (hfamily : ClassMembershipFamily g) (hcheck : assignmentCheck = true)
    (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    {m : Nat} (p : Snake m) :
    ∃ edge : Fin (m-8) → Fin (rows g).size, ∀ i,
      (sources g).toList[(edge i).val]? = some (actualState p i.val) ∧
      (targets g).toList[(edge i).val]? = some (actualState p (i.val+1)) :=
  actual_saved_walk h235 h236 (rows g) (sources g) (targets g)
    (defined_graph_covers g hfamily hcheck)
    (defined_endpoint_columns g).1 (defined_endpoint_columns g).2 p

#print axioms defined_graph_covers
#print axioms defined_endpoint_columns
#print axioms defined_actual_walk
end Snake9.DefinedGraph92
