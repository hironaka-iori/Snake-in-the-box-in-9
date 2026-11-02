import ContextAssignment
import ContextAssignmentLiteChecks

set_option maxRecDepth 100000

namespace Snake9.Batch92

/-- All literal data, default cases, overrides and class/root obligations agree
with the original assignment predicate. The finite check is kept separate. -/
theorem lite_assignmentAt_eq (di q : Nat) :
    Snake9.ContextLite92.assignmentAt di q = assignmentAt di q := by
  rfl

#print axioms lite_assignmentAt_eq
end Snake9.Batch92
