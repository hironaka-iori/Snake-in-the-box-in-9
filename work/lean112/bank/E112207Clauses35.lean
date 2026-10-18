import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1531 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1531)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 5 3 (meaning1455 q) (meaning1511 q) (meaning1531 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1511 = false ∨ valuation q 1531 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1532 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1532)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 5 4 (meaning1455 q) (meaning1512 q) (meaning1532 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1512 = false ∨ valuation q 1532 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1533 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1533)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 5 5 (meaning1455 q) (meaning1513 q) (meaning1533 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1513 = false ∨ valuation q 1533 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1534 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1534)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 5 6 (meaning1455 q) (meaning1514 q) (meaning1534 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1514 = false ∨ valuation q 1534 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1535 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1535)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 5 7 (meaning1455 q) (meaning1515 q) (meaning1535 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1515 = false ∨ valuation q 1535 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1536 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1536)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 5 8 (meaning1455 q) (meaning1516 q) (meaning1536 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1516 = false ∨ valuation q 1536 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1532 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1532)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 6 3 (meaning1456 q) (meaning1511 q) (meaning1532 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1511 = false ∨ valuation q 1532 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1533 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1533)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 6 4 (meaning1456 q) (meaning1512 q) (meaning1533 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1512 = false ∨ valuation q 1533 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1534 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1534)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 6 5 (meaning1456 q) (meaning1513 q) (meaning1534 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1513 = false ∨ valuation q 1534 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1535 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1535)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 6 6 (meaning1456 q) (meaning1514 q) (meaning1535 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1514 = false ∨ valuation q 1535 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1536 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1536)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 6 7 (meaning1456 q) (meaning1515 q) (meaning1536 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1515 = false ∨ valuation q 1536 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1533 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1533)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 7 3 (meaning1457 q) (meaning1511 q) (meaning1533 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1511 = false ∨ valuation q 1533 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1534 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1534)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 7 4 (meaning1457 q) (meaning1512 q) (meaning1534 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1512 = false ∨ valuation q 1534 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1535 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1535)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 7 5 (meaning1457 q) (meaning1513 q) (meaning1535 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1513 = false ∨ valuation q 1535 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1536 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1536)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 7 6 (meaning1457 q) (meaning1514 q) (meaning1536 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1514 = false ∨ valuation q 1536 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1534 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1534)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 8 3 (meaning1458 q) (meaning1511 q) (meaning1534 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1511 = false ∨ valuation q 1534 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1535 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1535)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 8 4 (meaning1458 q) (meaning1512 q) (meaning1535 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1512 = false ∨ valuation q 1535 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1536 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1536)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 8 5 (meaning1458 q) (meaning1513 q) (meaning1536 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1513 = false ∨ valuation q 1536 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1535 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1535)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 9 3 (meaning1459 q) (meaning1511 q) (meaning1535 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1511 = false ∨ valuation q 1535 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1536 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1536)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 10 3 (meaning1460 q) (meaning1511 q) (meaning1536 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1511 = false ∨ valuation q 1536 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1542 = true := by
  have hs : count1542 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1542)) (countLit q [-63]) (countLit q [-66]) (count1542 q) 1 (meaningNeg66 q) (meaning1542 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1542 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1542 = true := by
  have hs : count1542 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1542)) (countLit q [-63]) (countLit q [-66]) (count1542 q) 1 (meaningNeg63 q) (meaning1542 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1542 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1543 = true := by
  have hs : count1542 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1543)) (countLit q [-63]) (countLit q [-66]) (count1542 q) 1 1 (meaningNeg63 q) (meaningNeg66 q) (meaning1543 q) hs
  change (! (valuationOf q 63)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 66 = true ∨ valuation q 1543 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1544 = true := by
  have hs : count1544 q = (countLit q [-62]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -66])
  have hm := merge_right (literal (valuationOf q) (1542)) (literal (valuationOf q) (1544)) (countLit q [-62]) (countLit q [-63, -66]) (count1544 q) 1 (meaning1542 q) (meaning1544 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1544 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1545 = true := by
  have hs : count1544 q = (countLit q [-62]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -66])
  have hm := merge_right (literal (valuationOf q) (1543)) (literal (valuationOf q) (1545)) (countLit q [-62]) (countLit q [-63, -66]) (count1544 q) 2 (meaning1543 q) (meaning1545 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1545 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1544 = true := by
  have hs : count1544 q = (countLit q [-62]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -66])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (1544)) (countLit q [-62]) (countLit q [-63, -66]) (count1544 q) 1 (meaningNeg62 q) (meaning1544 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1544 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1542 = false ∨ valuationOf q 1545 = true := by
  have hs : count1544 q = (countLit q [-62]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -66])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1545)) (countLit q [-62]) (countLit q [-63, -66]) (count1544 q) 1 1 (meaningNeg62 q) (meaning1542 q) (meaning1545 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1542 = false ∨ valuation q 1545 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1543 = false ∨ valuationOf q 1546 = true := by
  have hs : count1544 q = (countLit q [-62]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -66])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1546)) (countLit q [-62]) (countLit q [-63, -66]) (count1544 q) 1 2 (meaningNeg62 q) (meaning1543 q) (meaning1546 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1543 = false ∨ valuation q 1546 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1547 = true := by
  have hs : count1547 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1547)) (countLit q [-69]) (countLit q [-71]) (count1547 q) 1 (meaningNeg71 q) (meaning1547 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1547 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1547 = true := by
  have hs : count1547 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1547)) (countLit q [-69]) (countLit q [-71]) (count1547 q) 1 (meaningNeg69 q) (meaning1547 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1547 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 71 = true ∨ valuationOf q 1548 = true := by
  have hs : count1547 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-71)) (literal (valuationOf q) (1548)) (countLit q [-69]) (countLit q [-71]) (count1547 q) 1 1 (meaningNeg69 q) (meaningNeg71 q) (meaning1548 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 71)) = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 71 = true ∨ valuation q 1548 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1549)) (countLit q [-72]) (countLit q [-74]) (count1549 q) 1 (meaningNeg74 q) (meaning1549 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1549 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E207.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112207
