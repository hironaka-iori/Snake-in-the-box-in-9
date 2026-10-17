import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1600 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_right (literal (valuationOf q) (1592)) (literal (valuationOf q) (1600)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 2 (meaning1592 q) (meaning1600 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1600 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1601 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_right (literal (valuationOf q) (1593)) (literal (valuationOf q) (1601)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 3 (meaning1593 q) (meaning1601 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1601 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1600 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1600)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 1 1 (meaning1568 q) (meaning1591 q) (meaning1600 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1591 = false ∨ valuation q 1600 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1601 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1601)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 1 2 (meaning1568 q) (meaning1592 q) (meaning1601 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1592 = false ∨ valuation q 1601 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1602 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1602)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 1 3 (meaning1568 q) (meaning1593 q) (meaning1602 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1593 = false ∨ valuation q 1602 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1603 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1603)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 1 4 (meaning1568 q) (meaning1594 q) (meaning1603 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1594 = false ∨ valuation q 1603 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1604 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1604)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 1 5 (meaning1568 q) (meaning1595 q) (meaning1604 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1595 = false ∨ valuation q 1604 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1601 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1601)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 2 1 (meaning1569 q) (meaning1591 q) (meaning1601 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1591 = false ∨ valuation q 1601 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1602 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1602)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 2 2 (meaning1569 q) (meaning1592 q) (meaning1602 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1592 = false ∨ valuation q 1602 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1603 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1603)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 2 3 (meaning1569 q) (meaning1593 q) (meaning1603 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1593 = false ∨ valuation q 1603 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1604 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1604)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 2 4 (meaning1569 q) (meaning1594 q) (meaning1604 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1594 = false ∨ valuation q 1604 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1601 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_left (literal (valuationOf q) (1570)) (literal (valuationOf q) (1601)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 3 (meaning1570 q) (meaning1601 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1601 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1602 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1602)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 3 1 (meaning1570 q) (meaning1591 q) (meaning1602 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1591 = false ∨ valuation q 1602 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1603 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1603)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 3 2 (meaning1570 q) (meaning1592 q) (meaning1603 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1592 = false ∨ valuation q 1603 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1604 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1604)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 3 3 (meaning1570 q) (meaning1593 q) (meaning1604 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1593 = false ∨ valuation q 1604 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1603 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1603)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 4 1 (meaning1571 q) (meaning1591 q) (meaning1603 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1591 = false ∨ valuation q 1603 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1604 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1604)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 4 2 (meaning1571 q) (meaning1592 q) (meaning1604 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1592 = false ∨ valuation q 1604 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1619 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1619)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 1 5 (meaning1541 q) (meaning1603 q) (meaning1619 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1603 = false ∨ valuation q 1619 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1617 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1617)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 2 2 (meaning1542 q) (meaning1600 q) (meaning1617 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1600 = false ∨ valuation q 1617 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1618 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1618)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 2 3 (meaning1542 q) (meaning1601 q) (meaning1618 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1601 = false ∨ valuation q 1618 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1619 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1619)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 2 4 (meaning1542 q) (meaning1602 q) (meaning1619 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1602 = false ∨ valuation q 1619 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1620 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1620)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 2 5 (meaning1542 q) (meaning1603 q) (meaning1620 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1603 = false ∨ valuation q 1620 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1621 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1621)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 2 6 (meaning1542 q) (meaning1604 q) (meaning1621 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1604 = false ∨ valuation q 1621 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1617 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1617)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 3 1 (meaning1543 q) (meaning1599 q) (meaning1617 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1599 = false ∨ valuation q 1617 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1618 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1618)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 3 2 (meaning1543 q) (meaning1600 q) (meaning1618 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1600 = false ∨ valuation q 1618 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1619 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1619)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 3 3 (meaning1543 q) (meaning1601 q) (meaning1619 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1601 = false ∨ valuation q 1619 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1620 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1620)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 3 4 (meaning1543 q) (meaning1602 q) (meaning1620 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1602 = false ∨ valuation q 1620 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1621 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1621)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 3 5 (meaning1543 q) (meaning1603 q) (meaning1621 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1603 = false ∨ valuation q 1621 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1622 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1622)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 3 6 (meaning1543 q) (meaning1604 q) (meaning1622 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1604 = false ∨ valuation q 1622 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1619 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1619)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 4 2 (meaning1544 q) (meaning1600 q) (meaning1619 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1600 = false ∨ valuation q 1619 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1620 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1620)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 4 3 (meaning1544 q) (meaning1601 q) (meaning1620 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1601 = false ∨ valuation q 1620 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1621 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1621)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 4 4 (meaning1544 q) (meaning1602 q) (meaning1621 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1602 = false ∨ valuation q 1621 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E254.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112254
