import LocalWindowTags
namespace Snake9.Witness118
open Snake9.LocalWindow
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/- Concrete count and path-component checks. Radius and endpoint census are checked separately in Python. -/

private def completedPaths : List (List Nat) := [[12, 14, 15, 7, 3, 1, 0, 32, 34, 42, 43, 41, 45, 173, 141, 133, 132, 134, 130, 138, 139], [112, 80, 81, 83, 87, 95, 94, 92, 124], [176, 144, 145, 147, 179, 51, 49, 53, 21, 29, 25, 27, 26, 18, 22, 54, 62, 63, 191, 159, 158, 156, 188], [224, 192, 193, 195, 227, 99, 97, 101, 69, 77, 73, 75, 74, 66, 70, 102, 110, 111, 239, 207, 206, 204, 236], [304, 272, 273, 275, 279, 287, 286, 284, 316], [352, 320, 321, 323, 327, 335, 334, 332, 364], [416, 384, 385, 387, 419, 291, 289, 293, 261, 269, 265, 267, 266, 258, 262, 294, 302, 303, 431, 399, 398, 396, 428]]
private def completedSet (v : Nat) : Bool := completedPaths.flatten.contains v

theorem completed_counts :
    [absentCorners completedSet 1 0 1, absentCorners completedSet 3 1 2,
      absentCorners completedSet 7 2 3, absentCorners completedSet 15 3 0,
      absentCorners completedSet 14 0 1] = [4, 2, 10, 2, 3] := by
  decide +kernel
#print axioms completed_counts

theorem completed_path_components :
    completedPaths.flatten.Nodup ∧
    completedPaths.flatten.all (fun v => decide (v < 512)) = true ∧
    ([0,1,3,7,15,14,12] : List Nat).all completedSet = true ∧
    completedPaths.all (fun path => decide (2 ≤ path.length) &&
      path.zipIdx.all (fun vi =>
        decide (cnt completedSet (nbrs vi.1) = if vi.2 = 0 ∨ vi.2+1 = path.length then 1 else 2) &&
        ((nbrs vi.1).filter completedSet).all (fun w => decide (
          (0 < vi.2 ∧ w = path.getD (vi.2-1) 512) ∨
          (vi.2+1 < path.length ∧ w = path.getD (vi.2+1) 512))))) = true ∧
    completedPaths.length = 7 := by
  decide +kernel
#print axioms completed_path_components

private def conditionalPaths : List (List Nat) := [[88, 92, 94, 95, 127, 63, 62, 54, 22, 18, 26, 27, 25, 29, 21, 85, 81, 83, 115, 51, 49, 305, 273, 275, 279, 287, 286, 284, 280], [110, 102, 70, 66, 74, 75, 73, 77, 109, 101, 37, 293, 261, 260, 262, 258, 266, 267, 265, 297, 41, 43, 42, 34, 32, 0, 1, 3, 7, 15, 14, 12, 44, 300, 302, 303, 367, 335, 334, 332, 328, 320, 321, 323, 355, 291], [176, 144, 145, 147, 151, 159, 158, 156, 188], [200, 204, 206, 207, 239, 175, 174, 166, 134, 130, 138, 139, 137, 141, 133, 197, 193, 195, 227, 163, 161, 417, 385, 387, 391, 399, 398, 396, 392]]
private def conditionalSet (v : Nat) : Bool := conditionalPaths.flatten.contains v

theorem conditional_counts :
    [absentCorners conditionalSet 1 0 1, absentCorners conditionalSet 3 1 2,
      absentCorners conditionalSet 7 2 3, absentCorners conditionalSet 15 3 0,
      absentCorners conditionalSet 14 0 1] = [4, 2, 10, 4, 2] := by
  decide +kernel
#print axioms conditional_counts

theorem conditional_path_components :
    conditionalPaths.flatten.Nodup ∧
    conditionalPaths.flatten.all (fun v => decide (v < 512)) = true ∧
    ([0,1,3,7,15,14,12] : List Nat).all conditionalSet = true ∧
    conditionalPaths.all (fun path => decide (2 ≤ path.length) &&
      path.zipIdx.all (fun vi =>
        decide (cnt conditionalSet (nbrs vi.1) = if vi.2 = 0 ∨ vi.2+1 = path.length then 1 else 2) &&
        ((nbrs vi.1).filter conditionalSet).all (fun w => decide (
          (0 < vi.2 ∧ w = path.getD (vi.2-1) 512) ∨
          (vi.2+1 < path.length ∧ w = path.getD (vi.2+1) 512))))) = true ∧
    conditionalPaths.length = 4 := by
  decide +kernel
#print axioms conditional_path_components

theorem coefficient_limit (a c : Nat) (h : 4*a+c ≤ 120) : min a c ≤ 24 := by
  omega

theorem completed_cycle_limit (a c : Nat) (h : 4*a+c ≤ 120) :
    2*(8745+2*min a c) ≤ 977*18 := by
  have := coefficient_limit a c h
  omega

theorem conditional_cycle_limit (a c : Nat) (h : 4*a+c ≤ 120) :
    1488+min a c ≤ 504*3 := by
  have := coefficient_limit a c h
  omega

theorem completed_comparison_barrier (p d R : Nat) (h : 2*p ≤ 977*d) :
    (4200*d+p)*235 ≤ 1098960*d+8*p+R := by
  omega

theorem conditional_comparison_barrier (p d R : Nat) (h : p ≤ 504*d) :
    (4200*d+p)*234 ≤ 1098960*d+8*p+R := by
  omega

#print axioms coefficient_limit
#print axioms completed_cycle_limit
#print axioms conditional_cycle_limit
#print axioms completed_comparison_barrier
#print axioms conditional_comparison_barrier
end Snake9.Witness118
