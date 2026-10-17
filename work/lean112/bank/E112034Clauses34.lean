import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 380 = false ∨ valuationOf q 508 = true := by
  have hs : count507 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (380)) (literal (valuationOf q) (508)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count507 q) 2 (meaning380 q) (meaning508 q) hs
  change valuationOf q 380 = false ∨ valuationOf q 508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 380 = false ∨ valuation q 508 = true := counterClause1089 (baseVal q)

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 508 = false := by
  rw [value508]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count507 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1540 = true := by
  have hs : count1540 q = (countLit q [-2]) + (countLit q [-3]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3])
  have hm := merge_right (literal (valuationOf q) (-3)) (literal (valuationOf q) (1540)) (countLit q [-2]) (countLit q [-3]) (count1540 q) 1 (meaningNeg3 q) (meaning1540 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1540 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1540 = true := by
  have hs : count1540 q = (countLit q [-2]) + (countLit q [-3]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1540)) (countLit q [-2]) (countLit q [-3]) (count1540 q) 1 (meaningNeg2 q) (meaning1540 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1540 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 3 = true ∨ valuationOf q 1541 = true := by
  have hs : count1540 q = (countLit q [-2]) + (countLit q [-3]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (-3)) (literal (valuationOf q) (1541)) (countLit q [-2]) (countLit q [-3]) (count1540 q) 1 1 (meaningNeg2 q) (meaningNeg3 q) (meaning1541 q) hs
  change (! (valuationOf q 2)) = false ∨ (! (valuationOf q 3)) = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 3 = true ∨ valuation q 1541 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1542 = true := by
  have hs : count1542 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1542)) (countLit q [-6]) (countLit q [-7]) (count1542 q) 1 (meaningNeg7 q) (meaning1542 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1542 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1543 = true := by
  have hs : count1542 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1543)) (countLit q [-6]) (countLit q [-7]) (count1542 q) 1 1 (meaningNeg6 q) (meaningNeg7 q) (meaning1543 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 1543 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1544 = true := by
  have hs : count1544 q = (countLit q [-2, -3]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2, -3]) (l₂ := [-6, -7])
  have hm := merge_right (literal (valuationOf q) (1542)) (literal (valuationOf q) (1544)) (countLit q [-2, -3]) (countLit q [-6, -7]) (count1544 q) 1 (meaning1542 q) (meaning1544 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1544 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1545 = true := by
  have hs : count1544 q = (countLit q [-2, -3]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2, -3]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1545)) (countLit q [-2, -3]) (countLit q [-6, -7]) (count1544 q) 1 1 (meaning1540 q) (meaning1542 q) (meaning1545 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1542 = false ∨ valuation q 1545 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1546 = true := by
  have hs : count1544 q = (countLit q [-2, -3]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2, -3]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1546)) (countLit q [-2, -3]) (countLit q [-6, -7]) (count1544 q) 1 2 (meaning1540 q) (meaning1543 q) (meaning1546 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1543 = false ∨ valuation q 1546 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1546 = true := by
  have hs : count1544 q = (countLit q [-2, -3]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2, -3]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1546)) (countLit q [-2, -3]) (countLit q [-6, -7]) (count1544 q) 2 1 (meaning1541 q) (meaning1542 q) (meaning1546 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1542 = false ∨ valuation q 1546 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1547 = true := by
  have hs : count1544 q = (countLit q [-2, -3]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2, -3]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1547)) (countLit q [-2, -3]) (countLit q [-6, -7]) (count1544 q) 2 2 (meaning1541 q) (meaning1543 q) (meaning1547 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1543 = false ∨ valuation q 1547 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1548 = true := by
  have hs : count1548 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1548)) (countLit q [-8]) (countLit q [-9]) (count1548 q) 1 (meaningNeg8 q) (meaning1548 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1548 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 9 = true ∨ valuationOf q 1549 = true := by
  have hs : count1548 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-9)) (literal (valuationOf q) (1549)) (countLit q [-8]) (countLit q [-9]) (count1548 q) 1 1 (meaningNeg8 q) (meaningNeg9 q) (meaning1549 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 9)) = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 9 = true ∨ valuation q 1549 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1550 = true := by
  have hs : count1550 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1550)) (countLit q [-11]) (countLit q [-13]) (count1550 q) 1 (meaningNeg11 q) (meaning1550 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1550 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1552 = true := by
  have hs : count1552 q = (countLit q [-8, -9]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-11, -13])
  have hm := merge_left (literal (valuationOf q) (1548)) (literal (valuationOf q) (1552)) (countLit q [-8, -9]) (countLit q [-11, -13]) (count1552 q) 1 (meaning1548 q) (meaning1552 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1552 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1553 = true := by
  have hs : count1552 q = (countLit q [-8, -9]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-11, -13])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1553)) (countLit q [-8, -9]) (countLit q [-11, -13]) (count1552 q) 1 1 (meaning1548 q) (meaning1550 q) (meaning1553 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1550 = false ∨ valuation q 1553 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1553 = true := by
  have hs : count1552 q = (countLit q [-8, -9]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-11, -13])
  have hm := merge_left (literal (valuationOf q) (1549)) (literal (valuationOf q) (1553)) (countLit q [-8, -9]) (countLit q [-11, -13]) (count1552 q) 2 (meaning1549 q) (meaning1553 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1553 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1554 = true := by
  have hs : count1552 q = (countLit q [-8, -9]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-11, -13])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1554)) (countLit q [-8, -9]) (countLit q [-11, -13]) (count1552 q) 2 1 (meaning1549 q) (meaning1550 q) (meaning1554 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1550 = false ∨ valuation q 1554 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1559 = true := by
  have hs : count1556 q = (countLit q [-2, -3, -6, -7]) + (countLit q [-8, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7]) (l₂ := [-8, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1559)) (countLit q [-2, -3, -6, -7]) (countLit q [-8, -9, -11, -13]) (count1556 q) 1 3 (meaning1544 q) (meaning1554 q) (meaning1559 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1554 = false ∨ valuation q 1559 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1558 = true := by
  have hs : count1556 q = (countLit q [-2, -3, -6, -7]) + (countLit q [-8, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7]) (l₂ := [-8, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1558)) (countLit q [-2, -3, -6, -7]) (countLit q [-8, -9, -11, -13]) (count1556 q) 2 1 (meaning1545 q) (meaning1552 q) (meaning1558 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1552 = false ∨ valuation q 1558 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1559 = true := by
  have hs : count1556 q = (countLit q [-2, -3, -6, -7]) + (countLit q [-8, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7]) (l₂ := [-8, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1559)) (countLit q [-2, -3, -6, -7]) (countLit q [-8, -9, -11, -13]) (count1556 q) 2 2 (meaning1545 q) (meaning1553 q) (meaning1559 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1553 = false ∨ valuation q 1559 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1560 = true := by
  have hs : count1556 q = (countLit q [-2, -3, -6, -7]) + (countLit q [-8, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7]) (l₂ := [-8, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1560)) (countLit q [-2, -3, -6, -7]) (countLit q [-8, -9, -11, -13]) (count1556 q) 2 3 (meaning1545 q) (meaning1554 q) (meaning1560 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1554 = false ∨ valuation q 1560 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1559 = true := by
  have hs : count1556 q = (countLit q [-2, -3, -6, -7]) + (countLit q [-8, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7]) (l₂ := [-8, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1559)) (countLit q [-2, -3, -6, -7]) (countLit q [-8, -9, -11, -13]) (count1556 q) 3 1 (meaning1546 q) (meaning1552 q) (meaning1559 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1552 = false ∨ valuation q 1559 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1560 = true := by
  have hs : count1556 q = (countLit q [-2, -3, -6, -7]) + (countLit q [-8, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7]) (l₂ := [-8, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1560)) (countLit q [-2, -3, -6, -7]) (countLit q [-8, -9, -11, -13]) (count1556 q) 3 2 (meaning1546 q) (meaning1553 q) (meaning1560 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1553 = false ∨ valuation q 1560 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1561 = true := by
  have hs : count1556 q = (countLit q [-2, -3, -6, -7]) + (countLit q [-8, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7]) (l₂ := [-8, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1561)) (countLit q [-2, -3, -6, -7]) (countLit q [-8, -9, -11, -13]) (count1556 q) 3 3 (meaning1546 q) (meaning1554 q) (meaning1561 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1554 = false ∨ valuation q 1561 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1560 = true := by
  have hs : count1556 q = (countLit q [-2, -3, -6, -7]) + (countLit q [-8, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7]) (l₂ := [-8, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1560)) (countLit q [-2, -3, -6, -7]) (countLit q [-8, -9, -11, -13]) (count1556 q) 4 1 (meaning1547 q) (meaning1552 q) (meaning1560 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1552 = false ∨ valuation q 1560 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1561 = true := by
  have hs : count1556 q = (countLit q [-2, -3, -6, -7]) + (countLit q [-8, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7]) (l₂ := [-8, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1561)) (countLit q [-2, -3, -6, -7]) (countLit q [-8, -9, -11, -13]) (count1556 q) 4 2 (meaning1547 q) (meaning1553 q) (meaning1561 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1553 = false ∨ valuation q 1561 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1562 = true := by
  have hs : count1556 q = (countLit q [-2, -3, -6, -7]) + (countLit q [-8, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7]) (l₂ := [-8, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1562)) (countLit q [-2, -3, -6, -7]) (countLit q [-8, -9, -11, -13]) (count1556 q) 4 3 (meaning1547 q) (meaning1554 q) (meaning1562 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1554 = false ∨ valuation q 1562 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-15]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16])
  have hm := merge_right (literal (valuationOf q) (-16)) (literal (valuationOf q) (1564)) (countLit q [-15]) (countLit q [-16]) (count1564 q) 1 (meaningNeg16 q) (meaning1564 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1564 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-15]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1564)) (countLit q [-15]) (countLit q [-16]) (count1564 q) 1 (meaningNeg15 q) (meaning1564 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1564 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 16 = true ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-15]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (-16)) (literal (valuationOf q) (1565)) (countLit q [-15]) (countLit q [-16]) (count1564 q) 1 1 (meaningNeg15 q) (meaningNeg16 q) (meaning1565 q) hs
  change (! (valuationOf q 15)) = false ∨ (! (valuationOf q 16)) = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 1565 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E034.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112034
