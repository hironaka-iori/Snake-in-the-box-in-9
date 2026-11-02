import ContextAssignmentLiteBridge

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Retained87

theorem assignment_data_sizes :
    defaultClasses.length = 505 ∧ savedBlockClasses.length = 791 ∧
    savedRoots.length = 127 ∧ recordedClassKeyLists.length = 127 ∧
    recordedClassRoots.length = 127 := by decide +kernel

theorem assignment_overrides :
    chosenClass 177 43 = 85 ∧ chosenClass 177 70 = 85 ∧ chosenClass 180 68 = 89 ∧
    chosenClass 177 0 = 84 ∧ chosenClass 180 0 = 88 := by decide +kernel

/-- Exactly 505 by 75 positions are tested; count codes are not enumerated. -/
theorem assignment_checked : assignmentCheck = true := by
  apply List.all_eq_true.mpr
  intro di hd
  apply List.all_eq_true.mpr
  intro q hq
  rw [← lite_assignmentAt_eq]
  exact Snake9.ContextLite92.assignmentAt_true di q (List.mem_range.mp hd) (List.mem_range.mp hq)

theorem source_context_assigned (di q : Nat) (hd : di < 505) (hq : q < 75)
    (hs : sourceCompatibleB di q = true) : Assigned di q :=
  assigned_of_check assignment_checked di q hd hq hs

theorem numeric_context_assigned (q di code : Nat) (hd : di < 505)
    (hk : numericKeep q di code = true) : Assigned di q := by
  have h := numeric_keep_source q di code hd hk
  exact source_context_assigned di q hd h.1 h.2.2

/-- The saved class and saved root equations remain in Assigned alongside
acceptance. Completion of the 127-class membership family remains a premise. -/
theorem numeric_context_membership (g : Diagram) (hfamily : ClassMembershipFamily g)
    (q di code : Nat) (hd : di < 505) (hk : numericKeep q di code = true) :
    Assigned di q ∧ diagramEval g (recordedClassRoot (chosenClass di q)) (digits code) = true :=
  numeric_membership_of_assignment g hfamily assignment_checked q di code hd hk

#print axioms assignment_data_sizes
#print axioms assignment_overrides
#print axioms assignment_checked
#print axioms source_context_assigned
#print axioms numeric_context_assigned
#print axioms numeric_context_membership
end Snake9.Batch92
