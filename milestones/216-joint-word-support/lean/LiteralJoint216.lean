import PathJoint216

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace LiteralJoint216
open PathJoint216

theorem common_neighbours_five_six :
    (List.range 64).filter (fun w => edge 5 w && edge w 6) = [4,7] := by
  decide +kernel

theorem independent_support_without_joint_support :
    let middle : List Nat := [19,21,22,25,26,28,35,37,38,41,42,44,55,59,61,62]
    middle.any (edge 5) = true ∧
      middle.any (fun w => edge w 6) = true ∧
      middle.any (fun w => edge 5 w && edge w 6) = false := by
  decide +kernel

#print axioms common_neighbours_five_six
#print axioms independent_support_without_joint_support
end LiteralJoint216
