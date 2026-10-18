import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1526 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1526)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 8 3 (meaning1450 q) (meaning1503 q) (meaning1526 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1503 = false ∨ valuation q 1526 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1527 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1527)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 8 4 (meaning1450 q) (meaning1504 q) (meaning1527 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1504 = false ∨ valuation q 1527 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1528 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1528)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 8 5 (meaning1450 q) (meaning1505 q) (meaning1528 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1505 = false ∨ valuation q 1528 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1529 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1529)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 8 6 (meaning1450 q) (meaning1506 q) (meaning1529 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1506 = false ∨ valuation q 1529 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (1535)) (countLit q [-60]) (countLit q [-62]) (count1535 q) 1 (meaningNeg62 q) (meaning1535 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1535 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1535)) (countLit q [-60]) (countLit q [-62]) (count1535 q) 1 (meaningNeg60 q) (meaning1535 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1535 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 62 = true ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (1536)) (countLit q [-60]) (countLit q [-62]) (count1535 q) 1 1 (meaningNeg60 q) (meaningNeg62 q) (meaning1536 q) hs
  change (! (valuationOf q 60)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 62 = true ∨ valuation q 1536 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-59]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60, -62])
  have hm := merge_right (literal (valuationOf q) (1535)) (literal (valuationOf q) (1537)) (countLit q [-59]) (countLit q [-60, -62]) (count1537 q) 1 (meaning1535 q) (meaning1537 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1537 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-59]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60, -62])
  have hm := merge_right (literal (valuationOf q) (1536)) (literal (valuationOf q) (1538)) (countLit q [-59]) (countLit q [-60, -62]) (count1537 q) 2 (meaning1536 q) (meaning1538 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1538 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-59]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60, -62])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1537)) (countLit q [-59]) (countLit q [-60, -62]) (count1537 q) 1 (meaningNeg59 q) (meaning1537 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1537 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1535 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-59]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60, -62])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1538)) (countLit q [-59]) (countLit q [-60, -62]) (count1537 q) 1 1 (meaningNeg59 q) (meaning1535 q) (meaning1538 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1535 = false ∨ valuation q 1538 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1536 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-59]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60, -62])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1539)) (countLit q [-59]) (countLit q [-60, -62]) (count1537 q) 1 2 (meaningNeg59 q) (meaning1536 q) (meaning1539 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1536 = false ∨ valuation q 1539 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1540 = true := by
  have hs : count1540 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1540)) (countLit q [-65]) (countLit q [-66]) (count1540 q) 1 (meaningNeg66 q) (meaning1540 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1540 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1540 = true := by
  have hs : count1540 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1540)) (countLit q [-65]) (countLit q [-66]) (count1540 q) 1 (meaningNeg65 q) (meaning1540 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1540 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1541 = true := by
  have hs : count1540 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1541)) (countLit q [-65]) (countLit q [-66]) (count1540 q) 1 1 (meaningNeg65 q) (meaningNeg66 q) (meaning1541 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 66 = true ∨ valuation q 1541 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1542 = true := by
  have hs : count1542 q = (countLit q [-68]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1542)) (countLit q [-68]) (countLit q [-70]) (count1542 q) 1 (meaningNeg70 q) (meaning1542 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1542 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1542 = true := by
  have hs : count1542 q = (countLit q [-68]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1542)) (countLit q [-68]) (countLit q [-70]) (count1542 q) 1 (meaningNeg68 q) (meaning1542 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1542 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 70 = true ∨ valuationOf q 1543 = true := by
  have hs : count1542 q = (countLit q [-68]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70])
  have hm := merge_two (literal (valuationOf q) (-68)) (literal (valuationOf q) (-70)) (literal (valuationOf q) (1543)) (countLit q [-68]) (countLit q [-70]) (count1542 q) 1 1 (meaningNeg68 q) (meaningNeg70 q) (meaning1543 q) hs
  change (! (valuationOf q 68)) = false ∨ (! (valuationOf q 70)) = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 70 = true ∨ valuation q 1543 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1544 = true := by
  have hs : count1544 q = (countLit q [-65, -66]) + (countLit q [-68, -70]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -70])
  have hm := merge_right (literal (valuationOf q) (1542)) (literal (valuationOf q) (1544)) (countLit q [-65, -66]) (countLit q [-68, -70]) (count1544 q) 1 (meaning1542 q) (meaning1544 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1544 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1545 = true := by
  have hs : count1544 q = (countLit q [-65, -66]) + (countLit q [-68, -70]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -70])
  have hm := merge_right (literal (valuationOf q) (1543)) (literal (valuationOf q) (1545)) (countLit q [-65, -66]) (countLit q [-68, -70]) (count1544 q) 2 (meaning1543 q) (meaning1545 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1545 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1544 = true := by
  have hs : count1544 q = (countLit q [-65, -66]) + (countLit q [-68, -70]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -70])
  have hm := merge_left (literal (valuationOf q) (1540)) (literal (valuationOf q) (1544)) (countLit q [-65, -66]) (countLit q [-68, -70]) (count1544 q) 1 (meaning1540 q) (meaning1544 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1544 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1545 = true := by
  have hs : count1544 q = (countLit q [-65, -66]) + (countLit q [-68, -70]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -70])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1545)) (countLit q [-65, -66]) (countLit q [-68, -70]) (count1544 q) 1 1 (meaning1540 q) (meaning1542 q) (meaning1545 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1542 = false ∨ valuation q 1545 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1546 = true := by
  have hs : count1544 q = (countLit q [-65, -66]) + (countLit q [-68, -70]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -70])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1546)) (countLit q [-65, -66]) (countLit q [-68, -70]) (count1544 q) 1 2 (meaning1540 q) (meaning1543 q) (meaning1546 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1543 = false ∨ valuation q 1546 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1545 = true := by
  have hs : count1544 q = (countLit q [-65, -66]) + (countLit q [-68, -70]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -70])
  have hm := merge_left (literal (valuationOf q) (1541)) (literal (valuationOf q) (1545)) (countLit q [-65, -66]) (countLit q [-68, -70]) (count1544 q) 2 (meaning1541 q) (meaning1545 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1545 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1546 = true := by
  have hs : count1544 q = (countLit q [-65, -66]) + (countLit q [-68, -70]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -70])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1546)) (countLit q [-65, -66]) (countLit q [-68, -70]) (count1544 q) 2 1 (meaning1541 q) (meaning1542 q) (meaning1546 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1542 = false ∨ valuation q 1546 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1547 = true := by
  have hs : count1544 q = (countLit q [-65, -66]) + (countLit q [-68, -70]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -70])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1547)) (countLit q [-65, -66]) (countLit q [-68, -70]) (count1544 q) 2 2 (meaning1541 q) (meaning1543 q) (meaning1547 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1543 = false ∨ valuation q 1547 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1548 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_right (literal (valuationOf q) (1544)) (literal (valuationOf q) (1548)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 1 (meaning1544 q) (meaning1548 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1548 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1549 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_right (literal (valuationOf q) (1545)) (literal (valuationOf q) (1549)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 2 (meaning1545 q) (meaning1549 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1549 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1550 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_right (literal (valuationOf q) (1546)) (literal (valuationOf q) (1550)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 3 (meaning1546 q) (meaning1550 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1550 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1551 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_right (literal (valuationOf q) (1547)) (literal (valuationOf q) (1551)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 4 (meaning1547 q) (meaning1551 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1551 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1548 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_left (literal (valuationOf q) (1537)) (literal (valuationOf q) (1548)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 1 (meaning1537 q) (meaning1548 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1548 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1549 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1549)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 1 1 (meaning1537 q) (meaning1544 q) (meaning1549 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1544 = false ∨ valuation q 1549 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E064.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112064
