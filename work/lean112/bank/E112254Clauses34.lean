import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1622 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1622)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 4 5 (meaning1544 q) (meaning1603 q) (meaning1622 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1603 = false ∨ valuation q 1622 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1623 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1623)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 4 6 (meaning1544 q) (meaning1604 q) (meaning1623 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1604 = false ∨ valuation q 1623 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1620 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1620)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 5 2 (meaning1545 q) (meaning1600 q) (meaning1620 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1600 = false ∨ valuation q 1620 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1621 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1621)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 5 3 (meaning1545 q) (meaning1601 q) (meaning1621 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1601 = false ∨ valuation q 1621 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1622 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1622)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 5 4 (meaning1545 q) (meaning1602 q) (meaning1622 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1602 = false ∨ valuation q 1622 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1623 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1623)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 5 5 (meaning1545 q) (meaning1603 q) (meaning1623 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1603 = false ∨ valuation q 1623 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1620 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1620)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 6 1 (meaning1546 q) (meaning1599 q) (meaning1620 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1599 = false ∨ valuation q 1620 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1621 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1621)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 6 2 (meaning1546 q) (meaning1600 q) (meaning1621 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1600 = false ∨ valuation q 1621 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1622 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1622)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 6 3 (meaning1546 q) (meaning1601 q) (meaning1622 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1601 = false ∨ valuation q 1622 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1623 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1623)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 6 4 (meaning1546 q) (meaning1602 q) (meaning1623 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1602 = false ∨ valuation q 1623 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1621 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1621)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 7 1 (meaning1547 q) (meaning1599 q) (meaning1621 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1599 = false ∨ valuation q 1621 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1622 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1622)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 7 2 (meaning1547 q) (meaning1600 q) (meaning1622 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1600 = false ∨ valuation q 1622 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1623 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1623)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 7 3 (meaning1547 q) (meaning1601 q) (meaning1623 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1601 = false ∨ valuation q 1623 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1622 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1622)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 8 1 (meaning1548 q) (meaning1599 q) (meaning1622 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1599 = false ∨ valuation q 1622 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1623 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1623)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 8 2 (meaning1548 q) (meaning1600 q) (meaning1623 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1600 = false ∨ valuation q 1623 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1623 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) + (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (l₂ := [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1623)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]) (countLit q [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (count1614 q) 9 1 (meaning1549 q) (meaning1599 q) (meaning1623 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1599 = false ∨ valuation q 1623 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (1632)) (countLit q [-66]) (countLit q [-67]) (count1632 q) 1 (meaningNeg67 q) (meaning1632 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1632 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1632)) (countLit q [-66]) (countLit q [-67]) (count1632 q) 1 (meaningNeg66 q) (meaning1632 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1632 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 67 = true ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-66)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (1633)) (countLit q [-66]) (countLit q [-67]) (count1632 q) 1 1 (meaningNeg66 q) (meaningNeg67 q) (meaning1633 q) hs
  change (! (valuationOf q 66)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 1633 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-65]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66, -67])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1634)) (countLit q [-65]) (countLit q [-66, -67]) (count1634 q) 1 (meaning1632 q) (meaning1634 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1634 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-65]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66, -67])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1635)) (countLit q [-65]) (countLit q [-66, -67]) (count1634 q) 2 (meaning1633 q) (meaning1635 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1635 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-65]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66, -67])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1634)) (countLit q [-65]) (countLit q [-66, -67]) (count1634 q) 1 (meaningNeg65 q) (meaning1634 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1634 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-65]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66, -67])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1635)) (countLit q [-65]) (countLit q [-66, -67]) (count1634 q) 1 1 (meaningNeg65 q) (meaning1632 q) (meaning1635 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1632 = false ∨ valuation q 1635 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-65]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66, -67])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1636)) (countLit q [-65]) (countLit q [-66, -67]) (count1634 q) 1 2 (meaningNeg65 q) (meaning1633 q) (meaning1636 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1633 = false ∨ valuation q 1636 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1637)) (countLit q [-69]) (countLit q [-70]) (count1637 q) 1 (meaningNeg70 q) (meaning1637 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1637 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1637)) (countLit q [-69]) (countLit q [-70]) (count1637 q) 1 (meaningNeg69 q) (meaning1637 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1637 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 70 = true ∨ valuationOf q 1638 = true := by
  have hs : count1637 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-70)) (literal (valuationOf q) (1638)) (countLit q [-69]) (countLit q [-70]) (count1637 q) 1 1 (meaningNeg69 q) (meaningNeg70 q) (meaning1638 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 70)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 1638 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1639)) (countLit q [-77]) (countLit q [-78]) (count1639 q) 1 (meaningNeg78 q) (meaning1639 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1639 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1639)) (countLit q [-77]) (countLit q [-78]) (count1639 q) 1 (meaningNeg77 q) (meaning1639 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1639 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 78 = true ∨ valuationOf q 1640 = true := by
  have hs : count1639 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-78)) (literal (valuationOf q) (1640)) (countLit q [-77]) (countLit q [-78]) (count1639 q) 1 1 (meaningNeg77 q) (meaningNeg78 q) (meaning1640 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 78)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 78 = true ∨ valuation q 1640 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-69, -70]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (1639)) (literal (valuationOf q) (1641)) (countLit q [-69, -70]) (countLit q [-77, -78]) (count1641 q) 1 (meaning1639 q) (meaning1641 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-69, -70]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (1640)) (literal (valuationOf q) (1642)) (countLit q [-69, -70]) (countLit q [-77, -78]) (count1641 q) 2 (meaning1640 q) (meaning1642 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1642 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E254.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112254
