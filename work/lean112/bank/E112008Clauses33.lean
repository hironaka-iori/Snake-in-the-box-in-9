import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1527 = true := by
  have hs : count1527 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1527)) (countLit q [-19]) (countLit q [-20]) (count1527 q) 1 (meaningNeg19 q) (meaning1527 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1527 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 20 = true ∨ valuationOf q 1528 = true := by
  have hs : count1527 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-20)) (literal (valuationOf q) (1528)) (countLit q [-19]) (countLit q [-20]) (count1527 q) 1 1 (meaningNeg19 q) (meaningNeg20 q) (meaning1528 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 20)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 20 = true ∨ valuation q 1528 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-14, -17]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -20])
  have hm := merge_right (literal (valuationOf q) (1527)) (literal (valuationOf q) (1529)) (countLit q [-14, -17]) (countLit q [-19, -20]) (count1529 q) 1 (meaning1527 q) (meaning1529 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1529 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-14, -17]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -20])
  have hm := merge_right (literal (valuationOf q) (1528)) (literal (valuationOf q) (1530)) (countLit q [-14, -17]) (countLit q [-19, -20]) (count1529 q) 2 (meaning1528 q) (meaning1530 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1530 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-14, -17]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -20])
  have hm := merge_left (literal (valuationOf q) (1525)) (literal (valuationOf q) (1529)) (countLit q [-14, -17]) (countLit q [-19, -20]) (count1529 q) 1 (meaning1525 q) (meaning1529 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1529 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-14, -17]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -20])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1530)) (countLit q [-14, -17]) (countLit q [-19, -20]) (count1529 q) 1 1 (meaning1525 q) (meaning1527 q) (meaning1530 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1527 = false ∨ valuation q 1530 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1531 = true := by
  have hs : count1529 q = (countLit q [-14, -17]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -20])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1531)) (countLit q [-14, -17]) (countLit q [-19, -20]) (count1529 q) 1 2 (meaning1525 q) (meaning1528 q) (meaning1531 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1528 = false ∨ valuation q 1531 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-14, -17]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -20])
  have hm := merge_left (literal (valuationOf q) (1526)) (literal (valuationOf q) (1530)) (countLit q [-14, -17]) (countLit q [-19, -20]) (count1529 q) 2 (meaning1526 q) (meaning1530 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1530 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1531 = true := by
  have hs : count1529 q = (countLit q [-14, -17]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -20])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1531)) (countLit q [-14, -17]) (countLit q [-19, -20]) (count1529 q) 2 1 (meaning1526 q) (meaning1527 q) (meaning1531 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1527 = false ∨ valuation q 1531 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1532 = true := by
  have hs : count1529 q = (countLit q [-14, -17]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -20])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1532)) (countLit q [-14, -17]) (countLit q [-19, -20]) (count1529 q) 2 2 (meaning1526 q) (meaning1528 q) (meaning1532 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1528 = false ∨ valuation q 1532 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-21]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1533)) (countLit q [-21]) (countLit q [-24]) (count1533 q) 1 (meaningNeg24 q) (meaning1533 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1533 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-21]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1534)) (countLit q [-21]) (countLit q [-24]) (count1533 q) 1 1 (meaningNeg21 q) (meaningNeg24 q) (meaning1534 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 24 = true ∨ valuation q 1534 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1535)) (countLit q [-25]) (countLit q [-26]) (count1535 q) 1 (meaningNeg25 q) (meaning1535 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1535 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-21, -24]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -26])
  have hm := merge_left (literal (valuationOf q) (1533)) (literal (valuationOf q) (1537)) (countLit q [-21, -24]) (countLit q [-25, -26]) (count1537 q) 1 (meaning1533 q) (meaning1537 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1537 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-21, -24]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1538)) (countLit q [-21, -24]) (countLit q [-25, -26]) (count1537 q) 1 1 (meaning1533 q) (meaning1535 q) (meaning1538 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1535 = false ∨ valuation q 1538 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-21, -24]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -26])
  have hm := merge_left (literal (valuationOf q) (1534)) (literal (valuationOf q) (1538)) (countLit q [-21, -24]) (countLit q [-25, -26]) (count1537 q) 2 (meaning1534 q) (meaning1538 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1538 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-21, -24]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1539)) (countLit q [-21, -24]) (countLit q [-25, -26]) (count1537 q) 2 1 (meaning1534 q) (meaning1535 q) (meaning1539 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1535 = false ∨ valuation q 1539 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1538)) (literal (valuationOf q) (1542)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 2 (meaning1538 q) (meaning1542 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1542 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1543 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1539)) (literal (valuationOf q) (1543)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 3 (meaning1539 q) (meaning1543 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1543 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1542)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 1 1 (meaning1529 q) (meaning1537 q) (meaning1542 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1537 = false ∨ valuation q 1542 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1543 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1543)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 1 2 (meaning1529 q) (meaning1538 q) (meaning1543 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1538 = false ∨ valuation q 1543 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1544)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 1 3 (meaning1529 q) (meaning1539 q) (meaning1544 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1539 = false ∨ valuation q 1544 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1543 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1543)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 2 1 (meaning1530 q) (meaning1537 q) (meaning1543 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1537 = false ∨ valuation q 1543 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1544)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 2 2 (meaning1530 q) (meaning1538 q) (meaning1544 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1538 = false ∨ valuation q 1544 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1545)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 2 3 (meaning1530 q) (meaning1539 q) (meaning1545 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1539 = false ∨ valuation q 1545 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1544)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 3 1 (meaning1531 q) (meaning1537 q) (meaning1544 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1537 = false ∨ valuation q 1544 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1545)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 3 2 (meaning1531 q) (meaning1538 q) (meaning1545 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1538 = false ∨ valuation q 1545 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1546)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 3 3 (meaning1531 q) (meaning1539 q) (meaning1546 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1539 = false ∨ valuation q 1546 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1545)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 4 1 (meaning1532 q) (meaning1537 q) (meaning1545 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1537 = false ∨ valuation q 1545 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1546)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 4 2 (meaning1532 q) (meaning1538 q) (meaning1546 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1538 = false ∨ valuation q 1546 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-14, -17, -19, -20]) + (countLit q [-21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -20]) (l₂ := [-21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1547)) (countLit q [-14, -17, -19, -20]) (countLit q [-21, -24, -25, -26]) (count1541 q) 4 3 (meaning1532 q) (meaning1539 q) (meaning1547 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1539 = false ∨ valuation q 1547 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1552 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1544)) (literal (valuationOf q) (1552)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 4 (meaning1544 q) (meaning1552 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1552 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E008.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112008
