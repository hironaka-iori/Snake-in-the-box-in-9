import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1511 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1511)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 1 2 (meaning1478 q) (meaning1502 q) (meaning1511 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1502 = false ∨ valuation q 1511 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1512 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1512)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 1 3 (meaning1478 q) (meaning1503 q) (meaning1512 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1503 = false ∨ valuation q 1512 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1513 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1513)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 1 4 (meaning1478 q) (meaning1504 q) (meaning1513 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1504 = false ∨ valuation q 1513 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1514 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1514)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 1 5 (meaning1478 q) (meaning1505 q) (meaning1514 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1505 = false ∨ valuation q 1514 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1512 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1512)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 2 2 (meaning1479 q) (meaning1502 q) (meaning1512 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1502 = false ∨ valuation q 1512 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1513 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1513)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 2 3 (meaning1479 q) (meaning1503 q) (meaning1513 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1503 = false ∨ valuation q 1513 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1514 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1514)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 2 4 (meaning1479 q) (meaning1504 q) (meaning1514 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1504 = false ∨ valuation q 1514 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1515 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1515)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 2 5 (meaning1479 q) (meaning1505 q) (meaning1515 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1505 = false ∨ valuation q 1515 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1516)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 2 6 (meaning1479 q) (meaning1506 q) (meaning1516 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1506 = false ∨ valuation q 1516 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1517)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 2 7 (meaning1479 q) (meaning1507 q) (meaning1517 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1507 = false ∨ valuation q 1517 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1513 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1513)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 3 2 (meaning1480 q) (meaning1502 q) (meaning1513 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1502 = false ∨ valuation q 1513 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1514 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1514)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 3 3 (meaning1480 q) (meaning1503 q) (meaning1514 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1503 = false ∨ valuation q 1514 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1515 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1515)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 3 4 (meaning1480 q) (meaning1504 q) (meaning1515 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1504 = false ∨ valuation q 1515 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1516)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 3 5 (meaning1480 q) (meaning1505 q) (meaning1516 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1505 = false ∨ valuation q 1516 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1517)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 3 6 (meaning1480 q) (meaning1506 q) (meaning1517 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1506 = false ∨ valuation q 1517 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1514 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1514)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 4 2 (meaning1481 q) (meaning1502 q) (meaning1514 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1502 = false ∨ valuation q 1514 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1532 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1532)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 1 8 (meaning1451 q) (meaning1516 q) (meaning1532 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1516 = false ∨ valuation q 1532 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1531 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1531)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 2 6 (meaning1452 q) (meaning1514 q) (meaning1531 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1514 = false ∨ valuation q 1531 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1532 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1532)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 2 7 (meaning1452 q) (meaning1515 q) (meaning1532 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1515 = false ∨ valuation q 1532 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1533 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1533)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 2 8 (meaning1452 q) (meaning1516 q) (meaning1533 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1516 = false ∨ valuation q 1533 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1534 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1534)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 2 9 (meaning1452 q) (meaning1517 q) (meaning1534 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1517 = false ∨ valuation q 1534 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1530 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1530)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 3 4 (meaning1453 q) (meaning1512 q) (meaning1530 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1512 = false ∨ valuation q 1530 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1531 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1531)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 3 5 (meaning1453 q) (meaning1513 q) (meaning1531 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1513 = false ∨ valuation q 1531 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1532 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1532)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 3 6 (meaning1453 q) (meaning1514 q) (meaning1532 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1514 = false ∨ valuation q 1532 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1533 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1533)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 3 7 (meaning1453 q) (meaning1515 q) (meaning1533 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1515 = false ∨ valuation q 1533 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1534 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1534)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 3 8 (meaning1453 q) (meaning1516 q) (meaning1534 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1516 = false ∨ valuation q 1534 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1535 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1535)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 3 9 (meaning1453 q) (meaning1517 q) (meaning1535 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1517 = false ∨ valuation q 1535 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1531 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1531)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 4 4 (meaning1454 q) (meaning1512 q) (meaning1531 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1512 = false ∨ valuation q 1531 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1532 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1532)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 4 5 (meaning1454 q) (meaning1513 q) (meaning1532 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1513 = false ∨ valuation q 1532 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1533 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1533)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 4 6 (meaning1454 q) (meaning1514 q) (meaning1533 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1514 = false ∨ valuation q 1533 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1534 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1534)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 4 7 (meaning1454 q) (meaning1515 q) (meaning1534 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1515 = false ∨ valuation q 1534 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1535 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1535)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 4 8 (meaning1454 q) (meaning1516 q) (meaning1535 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1516 = false ∨ valuation q 1535 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E207.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112207
