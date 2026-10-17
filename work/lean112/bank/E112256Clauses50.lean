import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec50 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1601 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1067 = true := by
  have hs : count1063 q = (countLit q [-93, -96, -101, -103]) + (countLit q [-105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103]) (l₂ := [-105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1052)) (literal (valuationOf q) (1061)) (literal (valuationOf q) (1067)) (countLit q [-93, -96, -101, -103]) (countLit q [-105, -106, -108, -109]) (count1063 q) 2 3 (meaning1052 q) (meaning1061 q) (meaning1067 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1067 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1601 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1061 = false ∨ valuation q 1067 = true := counterClause1601 (baseVal q)

theorem counterClause1602 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1068 = true := by
  have hs : count1063 q = (countLit q [-93, -96, -101, -103]) + (countLit q [-105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103]) (l₂ := [-105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1052)) (literal (valuationOf q) (1062)) (literal (valuationOf q) (1068)) (countLit q [-93, -96, -101, -103]) (countLit q [-105, -106, -108, -109]) (count1063 q) 2 4 (meaning1052 q) (meaning1062 q) (meaning1068 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1602 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1062 = false ∨ valuation q 1068 = true := counterClause1602 (baseVal q)

theorem counterClause1603 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1065 = true := by
  have hs : count1063 q = (countLit q [-93, -96, -101, -103]) + (countLit q [-105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103]) (l₂ := [-105, -106, -108, -109])
  have hm := merge_left (literal (valuationOf q) (1053)) (literal (valuationOf q) (1065)) (countLit q [-93, -96, -101, -103]) (countLit q [-105, -106, -108, -109]) (count1063 q) 3 (meaning1053 q) (meaning1065 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1065 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1603 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1065 = true := counterClause1603 (baseVal q)

theorem counterClause1604 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1066 = true := by
  have hs : count1063 q = (countLit q [-93, -96, -101, -103]) + (countLit q [-105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103]) (l₂ := [-105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1053)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1066)) (countLit q [-93, -96, -101, -103]) (countLit q [-105, -106, -108, -109]) (count1063 q) 3 1 (meaning1053 q) (meaning1059 q) (meaning1066 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1604 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1059 = false ∨ valuation q 1066 = true := counterClause1604 (baseVal q)

theorem counterClause1605 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1067 = true := by
  have hs : count1063 q = (countLit q [-93, -96, -101, -103]) + (countLit q [-105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103]) (l₂ := [-105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1053)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1067)) (countLit q [-93, -96, -101, -103]) (countLit q [-105, -106, -108, -109]) (count1063 q) 3 2 (meaning1053 q) (meaning1060 q) (meaning1067 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1067 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1605 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1060 = false ∨ valuation q 1067 = true := counterClause1605 (baseVal q)

theorem counterClause1606 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1068 = true := by
  have hs : count1063 q = (countLit q [-93, -96, -101, -103]) + (countLit q [-105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103]) (l₂ := [-105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1053)) (literal (valuationOf q) (1061)) (literal (valuationOf q) (1068)) (countLit q [-93, -96, -101, -103]) (countLit q [-105, -106, -108, -109]) (count1063 q) 3 3 (meaning1053 q) (meaning1061 q) (meaning1068 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1606 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1061 = false ∨ valuation q 1068 = true := counterClause1606 (baseVal q)

theorem counterClause1607 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1069 = true := by
  have hs : count1063 q = (countLit q [-93, -96, -101, -103]) + (countLit q [-105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103]) (l₂ := [-105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1053)) (literal (valuationOf q) (1062)) (literal (valuationOf q) (1069)) (countLit q [-93, -96, -101, -103]) (countLit q [-105, -106, -108, -109]) (count1063 q) 3 4 (meaning1053 q) (meaning1062 q) (meaning1069 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1069 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1607 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1062 = false ∨ valuation q 1069 = true := counterClause1607 (baseVal q)

theorem counterClause1608 (q : Nat → Bool) : valuationOf q 1054 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1067 = true := by
  have hs : count1063 q = (countLit q [-93, -96, -101, -103]) + (countLit q [-105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103]) (l₂ := [-105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1054)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1067)) (countLit q [-93, -96, -101, -103]) (countLit q [-105, -106, -108, -109]) (count1063 q) 4 1 (meaning1054 q) (meaning1059 q) (meaning1067 q) hs
  change valuationOf q 1054 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1067 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1608 (q : Snake 81) (h : Conditions q) : valuation q 1054 = false ∨ valuation q 1059 = false ∨ valuation q 1067 = true := counterClause1608 (baseVal q)

theorem counterClause1609 (q : Nat → Bool) : valuationOf q 1054 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1068 = true := by
  have hs : count1063 q = (countLit q [-93, -96, -101, -103]) + (countLit q [-105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103]) (l₂ := [-105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1054)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1068)) (countLit q [-93, -96, -101, -103]) (countLit q [-105, -106, -108, -109]) (count1063 q) 4 2 (meaning1054 q) (meaning1060 q) (meaning1068 q) hs
  change valuationOf q 1054 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1609 (q : Snake 81) (h : Conditions q) : valuation q 1054 = false ∨ valuation q 1060 = false ∨ valuation q 1068 = true := counterClause1609 (baseVal q)

theorem counterClause1610 (q : Nat → Bool) : valuationOf q 1054 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1069 = true := by
  have hs : count1063 q = (countLit q [-93, -96, -101, -103]) + (countLit q [-105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103]) (l₂ := [-105, -106, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1054)) (literal (valuationOf q) (1061)) (literal (valuationOf q) (1069)) (countLit q [-93, -96, -101, -103]) (countLit q [-105, -106, -108, -109]) (count1063 q) 4 3 (meaning1054 q) (meaning1061 q) (meaning1069 q) hs
  change valuationOf q 1054 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1069 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1610 (q : Snake 81) (h : Conditions q) : valuation q 1054 = false ∨ valuation q 1061 = false ∨ valuation q 1069 = true := counterClause1610 (baseVal q)

theorem counterClause1611 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1071 = true := by
  have hs : count1071 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1071)) (countLit q [-111]) (countLit q [-113]) (count1071 q) 1 (meaningNeg113 q) (meaning1071 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1071 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1611 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1071 = true := counterClause1611 (baseVal q)

theorem counterClause1612 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1071 = true := by
  have hs : count1071 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1071)) (countLit q [-111]) (countLit q [-113]) (count1071 q) 1 (meaningNeg111 q) (meaning1071 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1071 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1612 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1071 = true := counterClause1612 (baseVal q)

theorem counterClause1613 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1072 = true := by
  have hs : count1071 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1072)) (countLit q [-111]) (countLit q [-113]) (count1071 q) 1 1 (meaningNeg111 q) (meaningNeg113 q) (meaning1072 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1072 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1613 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 1072 = true := counterClause1613 (baseVal q)

theorem counterClause1614 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1073 = true := by
  have hs : count1073 q = (countLit q [-116]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-118])
  have hm := merge_right (literal (valuationOf q) (-118)) (literal (valuationOf q) (1073)) (countLit q [-116]) (countLit q [-118]) (count1073 q) 1 (meaningNeg118 q) (meaning1073 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1073 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1614 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1073 = true := counterClause1614 (baseVal q)

theorem counterClause1615 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1073 = true := by
  have hs : count1073 q = (countLit q [-116]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-118])
  have hm := merge_left (literal (valuationOf q) (-116)) (literal (valuationOf q) (1073)) (countLit q [-116]) (countLit q [-118]) (count1073 q) 1 (meaningNeg116 q) (meaning1073 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1073 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1615 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1073 = true := counterClause1615 (baseVal q)

theorem counterClause1616 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 118 = true ∨ valuationOf q 1074 = true := by
  have hs : count1073 q = (countLit q [-116]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-118])
  have hm := merge_two (literal (valuationOf q) (-116)) (literal (valuationOf q) (-118)) (literal (valuationOf q) (1074)) (countLit q [-116]) (countLit q [-118]) (count1073 q) 1 1 (meaningNeg116 q) (meaningNeg118 q) (meaning1074 q) hs
  change (! (valuationOf q 116)) = false ∨ (! (valuationOf q 118)) = false ∨ valuationOf q 1074 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1616 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 118 = true ∨ valuation q 1074 = true := counterClause1616 (baseVal q)

theorem counterClause1617 (q : Nat → Bool) : valuationOf q 1073 = false ∨ valuationOf q 1075 = true := by
  have hs : count1075 q = (countLit q [-111, -113]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-116, -118])
  have hm := merge_right (literal (valuationOf q) (1073)) (literal (valuationOf q) (1075)) (countLit q [-111, -113]) (countLit q [-116, -118]) (count1075 q) 1 (meaning1073 q) (meaning1075 q) hs
  change valuationOf q 1073 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1617 (q : Snake 81) (h : Conditions q) : valuation q 1073 = false ∨ valuation q 1075 = true := counterClause1617 (baseVal q)

theorem counterClause1618 (q : Nat → Bool) : valuationOf q 1074 = false ∨ valuationOf q 1076 = true := by
  have hs : count1075 q = (countLit q [-111, -113]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-116, -118])
  have hm := merge_right (literal (valuationOf q) (1074)) (literal (valuationOf q) (1076)) (countLit q [-111, -113]) (countLit q [-116, -118]) (count1075 q) 2 (meaning1074 q) (meaning1076 q) hs
  change valuationOf q 1074 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1618 (q : Snake 81) (h : Conditions q) : valuation q 1074 = false ∨ valuation q 1076 = true := counterClause1618 (baseVal q)

theorem counterClause1619 (q : Nat → Bool) : valuationOf q 1071 = false ∨ valuationOf q 1075 = true := by
  have hs : count1075 q = (countLit q [-111, -113]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-116, -118])
  have hm := merge_left (literal (valuationOf q) (1071)) (literal (valuationOf q) (1075)) (countLit q [-111, -113]) (countLit q [-116, -118]) (count1075 q) 1 (meaning1071 q) (meaning1075 q) hs
  change valuationOf q 1071 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1619 (q : Snake 81) (h : Conditions q) : valuation q 1071 = false ∨ valuation q 1075 = true := counterClause1619 (baseVal q)

theorem counterClause1620 (q : Nat → Bool) : valuationOf q 1071 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1076 = true := by
  have hs : count1075 q = (countLit q [-111, -113]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-116, -118])
  have hm := merge_two (literal (valuationOf q) (1071)) (literal (valuationOf q) (1073)) (literal (valuationOf q) (1076)) (countLit q [-111, -113]) (countLit q [-116, -118]) (count1075 q) 1 1 (meaning1071 q) (meaning1073 q) (meaning1076 q) hs
  change valuationOf q 1071 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1620 (q : Snake 81) (h : Conditions q) : valuation q 1071 = false ∨ valuation q 1073 = false ∨ valuation q 1076 = true := counterClause1620 (baseVal q)

theorem counterClause1621 (q : Nat → Bool) : valuationOf q 1071 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1077 = true := by
  have hs : count1075 q = (countLit q [-111, -113]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-116, -118])
  have hm := merge_two (literal (valuationOf q) (1071)) (literal (valuationOf q) (1074)) (literal (valuationOf q) (1077)) (countLit q [-111, -113]) (countLit q [-116, -118]) (count1075 q) 1 2 (meaning1071 q) (meaning1074 q) (meaning1077 q) hs
  change valuationOf q 1071 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1621 (q : Snake 81) (h : Conditions q) : valuation q 1071 = false ∨ valuation q 1074 = false ∨ valuation q 1077 = true := counterClause1621 (baseVal q)

theorem counterClause1622 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1076 = true := by
  have hs : count1075 q = (countLit q [-111, -113]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-116, -118])
  have hm := merge_left (literal (valuationOf q) (1072)) (literal (valuationOf q) (1076)) (countLit q [-111, -113]) (countLit q [-116, -118]) (count1075 q) 2 (meaning1072 q) (meaning1076 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1622 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1076 = true := counterClause1622 (baseVal q)

theorem counterClause1623 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1077 = true := by
  have hs : count1075 q = (countLit q [-111, -113]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-116, -118])
  have hm := merge_two (literal (valuationOf q) (1072)) (literal (valuationOf q) (1073)) (literal (valuationOf q) (1077)) (countLit q [-111, -113]) (countLit q [-116, -118]) (count1075 q) 2 1 (meaning1072 q) (meaning1073 q) (meaning1077 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1623 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1073 = false ∨ valuation q 1077 = true := counterClause1623 (baseVal q)

theorem counterClause1624 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 1079 = true := by
  have hs : count1079 q = (countLit q [-120]) + (countLit q [-122]) := List.countP_append (p := literal q) (l₁ := [-120]) (l₂ := [-122])
  have hm := merge_right (literal (valuationOf q) (-122)) (literal (valuationOf q) (1079)) (countLit q [-120]) (countLit q [-122]) (count1079 q) 1 (meaningNeg122 q) (meaning1079 q) hs
  change (! (valuationOf q 122)) = false ∨ valuationOf q 1079 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1624 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1079 = true := counterClause1624 (baseVal q)

theorem counterClause1625 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 1079 = true := by
  have hs : count1079 q = (countLit q [-120]) + (countLit q [-122]) := List.countP_append (p := literal q) (l₁ := [-120]) (l₂ := [-122])
  have hm := merge_left (literal (valuationOf q) (-120)) (literal (valuationOf q) (1079)) (countLit q [-120]) (countLit q [-122]) (count1079 q) 1 (meaningNeg120 q) (meaning1079 q) hs
  change (! (valuationOf q 120)) = false ∨ valuationOf q 1079 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1625 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 1079 = true := counterClause1625 (baseVal q)

theorem counterClause1626 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 122 = true ∨ valuationOf q 1080 = true := by
  have hs : count1079 q = (countLit q [-120]) + (countLit q [-122]) := List.countP_append (p := literal q) (l₁ := [-120]) (l₂ := [-122])
  have hm := merge_two (literal (valuationOf q) (-120)) (literal (valuationOf q) (-122)) (literal (valuationOf q) (1080)) (countLit q [-120]) (countLit q [-122]) (count1079 q) 1 1 (meaningNeg120 q) (meaningNeg122 q) (meaning1080 q) hs
  change (! (valuationOf q 120)) = false ∨ (! (valuationOf q 122)) = false ∨ valuationOf q 1080 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1626 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 122 = true ∨ valuation q 1080 = true := counterClause1626 (baseVal q)

theorem counterClause1627 (q : Nat → Bool) : valuationOf q 126 = true ∨ valuationOf q 1081 = true := by
  have hs : count1081 q = (countLit q [-124]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-126])
  have hm := merge_right (literal (valuationOf q) (-126)) (literal (valuationOf q) (1081)) (countLit q [-124]) (countLit q [-126]) (count1081 q) 1 (meaningNeg126 q) (meaning1081 q) hs
  change (! (valuationOf q 126)) = false ∨ valuationOf q 1081 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1627 (q : Snake 81) (h : Conditions q) : valuation q 126 = true ∨ valuation q 1081 = true := counterClause1627 (baseVal q)

theorem counterClause1628 (q : Nat → Bool) : valuationOf q 124 = true ∨ valuationOf q 1081 = true := by
  have hs : count1081 q = (countLit q [-124]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-126])
  have hm := merge_left (literal (valuationOf q) (-124)) (literal (valuationOf q) (1081)) (countLit q [-124]) (countLit q [-126]) (count1081 q) 1 (meaningNeg124 q) (meaning1081 q) hs
  change (! (valuationOf q 124)) = false ∨ valuationOf q 1081 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1628 (q : Snake 81) (h : Conditions q) : valuation q 124 = true ∨ valuation q 1081 = true := counterClause1628 (baseVal q)

theorem counterClause1629 (q : Nat → Bool) : valuationOf q 124 = true ∨ valuationOf q 126 = true ∨ valuationOf q 1082 = true := by
  have hs : count1081 q = (countLit q [-124]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-126])
  have hm := merge_two (literal (valuationOf q) (-124)) (literal (valuationOf q) (-126)) (literal (valuationOf q) (1082)) (countLit q [-124]) (countLit q [-126]) (count1081 q) 1 1 (meaningNeg124 q) (meaningNeg126 q) (meaning1082 q) hs
  change (! (valuationOf q 124)) = false ∨ (! (valuationOf q 126)) = false ∨ valuationOf q 1082 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1629 (q : Snake 81) (h : Conditions q) : valuation q 124 = true ∨ valuation q 126 = true ∨ valuation q 1082 = true := counterClause1629 (baseVal q)

theorem counterClause1630 (q : Nat → Bool) : valuationOf q 1081 = false ∨ valuationOf q 1083 = true := by
  have hs : count1083 q = (countLit q [-120, -122]) + (countLit q [-124, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -122]) (l₂ := [-124, -126])
  have hm := merge_right (literal (valuationOf q) (1081)) (literal (valuationOf q) (1083)) (countLit q [-120, -122]) (countLit q [-124, -126]) (count1083 q) 1 (meaning1081 q) (meaning1083 q) hs
  change valuationOf q 1081 = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1630 (q : Snake 81) (h : Conditions q) : valuation q 1081 = false ∨ valuation q 1083 = true := counterClause1630 (baseVal q)

theorem counterClause1631 (q : Nat → Bool) : valuationOf q 1082 = false ∨ valuationOf q 1084 = true := by
  have hs : count1083 q = (countLit q [-120, -122]) + (countLit q [-124, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -122]) (l₂ := [-124, -126])
  have hm := merge_right (literal (valuationOf q) (1082)) (literal (valuationOf q) (1084)) (countLit q [-120, -122]) (countLit q [-124, -126]) (count1083 q) 2 (meaning1082 q) (meaning1084 q) hs
  change valuationOf q 1082 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1631 (q : Snake 81) (h : Conditions q) : valuation q 1082 = false ∨ valuation q 1084 = true := counterClause1631 (baseVal q)

theorem counterClause1632 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1083 = true := by
  have hs : count1083 q = (countLit q [-120, -122]) + (countLit q [-124, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -122]) (l₂ := [-124, -126])
  have hm := merge_left (literal (valuationOf q) (1079)) (literal (valuationOf q) (1083)) (countLit q [-120, -122]) (countLit q [-124, -126]) (count1083 q) 1 (meaning1079 q) (meaning1083 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1632 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1083 = true := counterClause1632 (baseVal q)

theorem block50 (q : Snake 81) (h : Conditions q) : B112E256.Block50 (valuation q) :=
  ⟨clause1601 q h, clause1602 q h, clause1603 q h, clause1604 q h, clause1605 q h, clause1606 q h, clause1607 q h, clause1608 q h, clause1609 q h, clause1610 q h, clause1611 q h, clause1612 q h, clause1613 q h, clause1614 q h, clause1615 q h, clause1616 q h, clause1617 q h, clause1618 q h, clause1619 q h, clause1620 q h, clause1621 q h, clause1622 q h, clause1623 q h, clause1624 q h, clause1625 q h, clause1626 q h, clause1627 q h, clause1628 q h, clause1629 q h, clause1630 q h, clause1631 q h, clause1632 q h⟩

end
end Snake9.Regrowth.E112256
