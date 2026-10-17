import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 505 = false ∨ valuationOf q 508 = true := by
  have hs : count507 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_two (literal (valuationOf q) (379)) (literal (valuationOf q) (505)) (literal (valuationOf q) (508)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count507 q) 1 1 (meaning379 q) (meaning505 q) (meaning508 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 505 = false ∨ valuationOf q 508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 505 = false ∨ valuation q 508 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 380 = false ∨ valuationOf q 508 = true := by
  have hs : count507 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (380)) (literal (valuationOf q) (508)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count507 q) 2 (meaning380 q) (meaning508 q) hs
  change valuationOf q 380 = false ∨ valuationOf q 508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 380 = false ∨ valuation q 508 = true := counterClause994 (baseVal q)

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 508 = false := by
  rw [value508]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count507 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause996 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1547 = true := by
  have hs : count1547 q = (countLit q [-2]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4])
  have hm := merge_right (literal (valuationOf q) (-4)) (literal (valuationOf q) (1547)) (countLit q [-2]) (countLit q [-4]) (count1547 q) 1 (meaningNeg4 q) (meaning1547 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1547 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1547 = true := by
  have hs : count1547 q = (countLit q [-2]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1547)) (countLit q [-2]) (countLit q [-4]) (count1547 q) 1 (meaningNeg2 q) (meaning1547 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1547 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 4 = true ∨ valuationOf q 1548 = true := by
  have hs : count1547 q = (countLit q [-2]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (-4)) (literal (valuationOf q) (1548)) (countLit q [-2]) (countLit q [-4]) (count1547 q) 1 1 (meaningNeg2 q) (meaningNeg4 q) (meaning1548 q) hs
  change (! (valuationOf q 2)) = false ∨ (! (valuationOf q 4)) = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 4 = true ∨ valuation q 1548 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-7]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-8])
  have hm := merge_right (literal (valuationOf q) (-8)) (literal (valuationOf q) (1549)) (countLit q [-7]) (countLit q [-8]) (count1549 q) 1 (meaningNeg8 q) (meaning1549 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1549 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-7]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-8])
  have hm := merge_left (literal (valuationOf q) (-7)) (literal (valuationOf q) (1549)) (countLit q [-7]) (countLit q [-8]) (count1549 q) 1 (meaningNeg7 q) (meaning1549 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1549 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 8 = true ∨ valuationOf q 1550 = true := by
  have hs : count1549 q = (countLit q [-7]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-8])
  have hm := merge_two (literal (valuationOf q) (-7)) (literal (valuationOf q) (-8)) (literal (valuationOf q) (1550)) (countLit q [-7]) (countLit q [-8]) (count1549 q) 1 1 (meaningNeg7 q) (meaningNeg8 q) (meaning1550 q) hs
  change (! (valuationOf q 7)) = false ∨ (! (valuationOf q 8)) = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 8 = true ∨ valuation q 1550 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-2, -4]) + (countLit q [-7, -8]) := List.countP_append (p := literal q) (l₁ := [-2, -4]) (l₂ := [-7, -8])
  have hm := merge_right (literal (valuationOf q) (1549)) (literal (valuationOf q) (1551)) (countLit q [-2, -4]) (countLit q [-7, -8]) (count1551 q) 1 (meaning1549 q) (meaning1551 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1551 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1552 = true := by
  have hs : count1551 q = (countLit q [-2, -4]) + (countLit q [-7, -8]) := List.countP_append (p := literal q) (l₁ := [-2, -4]) (l₂ := [-7, -8])
  have hm := merge_right (literal (valuationOf q) (1550)) (literal (valuationOf q) (1552)) (countLit q [-2, -4]) (countLit q [-7, -8]) (count1551 q) 2 (meaning1550 q) (meaning1552 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1552 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-2, -4]) + (countLit q [-7, -8]) := List.countP_append (p := literal q) (l₁ := [-2, -4]) (l₂ := [-7, -8])
  have hm := merge_left (literal (valuationOf q) (1547)) (literal (valuationOf q) (1551)) (countLit q [-2, -4]) (countLit q [-7, -8]) (count1551 q) 1 (meaning1547 q) (meaning1551 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1551 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1552 = true := by
  have hs : count1551 q = (countLit q [-2, -4]) + (countLit q [-7, -8]) := List.countP_append (p := literal q) (l₁ := [-2, -4]) (l₂ := [-7, -8])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1552)) (countLit q [-2, -4]) (countLit q [-7, -8]) (count1551 q) 1 1 (meaning1547 q) (meaning1549 q) (meaning1552 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1549 = false ∨ valuation q 1552 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1553 = true := by
  have hs : count1551 q = (countLit q [-2, -4]) + (countLit q [-7, -8]) := List.countP_append (p := literal q) (l₁ := [-2, -4]) (l₂ := [-7, -8])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1553)) (countLit q [-2, -4]) (countLit q [-7, -8]) (count1551 q) 1 2 (meaning1547 q) (meaning1550 q) (meaning1553 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1550 = false ∨ valuation q 1553 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1552 = true := by
  have hs : count1551 q = (countLit q [-2, -4]) + (countLit q [-7, -8]) := List.countP_append (p := literal q) (l₁ := [-2, -4]) (l₂ := [-7, -8])
  have hm := merge_left (literal (valuationOf q) (1548)) (literal (valuationOf q) (1552)) (countLit q [-2, -4]) (countLit q [-7, -8]) (count1551 q) 2 (meaning1548 q) (meaning1552 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1552 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1553 = true := by
  have hs : count1551 q = (countLit q [-2, -4]) + (countLit q [-7, -8]) := List.countP_append (p := literal q) (l₁ := [-2, -4]) (l₂ := [-7, -8])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1553)) (countLit q [-2, -4]) (countLit q [-7, -8]) (count1551 q) 2 1 (meaning1548 q) (meaning1549 q) (meaning1553 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1549 = false ∨ valuation q 1553 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1554 = true := by
  have hs : count1551 q = (countLit q [-2, -4]) + (countLit q [-7, -8]) := List.countP_append (p := literal q) (l₁ := [-2, -4]) (l₂ := [-7, -8])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1554)) (countLit q [-2, -4]) (countLit q [-7, -8]) (count1551 q) 2 2 (meaning1548 q) (meaning1550 q) (meaning1554 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1550 = false ∨ valuation q 1554 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (1555)) (countLit q [-9]) (countLit q [-11]) (count1555 q) 1 (meaningNeg11 q) (meaning1555 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1555 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (1555)) (countLit q [-9]) (countLit q [-11]) (count1555 q) 1 (meaningNeg9 q) (meaning1555 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1555 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 11 = true ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-11)) (literal (valuationOf q) (1556)) (countLit q [-9]) (countLit q [-11]) (count1555 q) 1 1 (meaningNeg9 q) (meaningNeg11 q) (meaning1556 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 11)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 11 = true ∨ valuation q 1556 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1557 = true := by
  have hs : count1557 q = (countLit q [-13]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-16])
  have hm := merge_right (literal (valuationOf q) (-16)) (literal (valuationOf q) (1557)) (countLit q [-13]) (countLit q [-16]) (count1557 q) 1 (meaningNeg16 q) (meaning1557 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1557 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1557 = true := by
  have hs : count1557 q = (countLit q [-13]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-16])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1557)) (countLit q [-13]) (countLit q [-16]) (count1557 q) 1 (meaningNeg13 q) (meaning1557 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1557 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 16 = true ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-13]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-16])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-16)) (literal (valuationOf q) (1558)) (countLit q [-13]) (countLit q [-16]) (count1557 q) 1 1 (meaningNeg13 q) (meaningNeg16 q) (meaning1558 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 16)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 1558 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1559 = true := by
  have hs : count1559 q = (countLit q [-9, -11]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -16])
  have hm := merge_right (literal (valuationOf q) (1557)) (literal (valuationOf q) (1559)) (countLit q [-9, -11]) (countLit q [-13, -16]) (count1559 q) 1 (meaning1557 q) (meaning1559 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1559 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-9, -11]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -16])
  have hm := merge_right (literal (valuationOf q) (1558)) (literal (valuationOf q) (1560)) (countLit q [-9, -11]) (countLit q [-13, -16]) (count1559 q) 2 (meaning1558 q) (meaning1560 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1560 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1559 = true := by
  have hs : count1559 q = (countLit q [-9, -11]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -16])
  have hm := merge_left (literal (valuationOf q) (1555)) (literal (valuationOf q) (1559)) (countLit q [-9, -11]) (countLit q [-13, -16]) (count1559 q) 1 (meaning1555 q) (meaning1559 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1559 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-9, -11]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -16])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1560)) (countLit q [-9, -11]) (countLit q [-13, -16]) (count1559 q) 1 1 (meaning1555 q) (meaning1557 q) (meaning1560 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1557 = false ∨ valuation q 1560 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true := by
  have hs : count1559 q = (countLit q [-9, -11]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -16])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1561)) (countLit q [-9, -11]) (countLit q [-13, -16]) (count1559 q) 1 2 (meaning1555 q) (meaning1558 q) (meaning1561 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1558 = false ∨ valuation q 1561 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-9, -11]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -16])
  have hm := merge_left (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-9, -11]) (countLit q [-13, -16]) (count1559 q) 2 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1561 = true := by
  have hs : count1559 q = (countLit q [-9, -11]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -16])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1561)) (countLit q [-9, -11]) (countLit q [-13, -16]) (count1559 q) 2 1 (meaning1556 q) (meaning1557 q) (meaning1561 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1557 = false ∨ valuation q 1561 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true := by
  have hs : count1559 q = (countLit q [-9, -11]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -16])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1562)) (countLit q [-9, -11]) (countLit q [-13, -16]) (count1559 q) 2 2 (meaning1556 q) (meaning1558 q) (meaning1562 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1558 = false ∨ valuation q 1562 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1563 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_right (literal (valuationOf q) (1559)) (literal (valuationOf q) (1563)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 1 (meaning1559 q) (meaning1563 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1563 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E036.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112036
