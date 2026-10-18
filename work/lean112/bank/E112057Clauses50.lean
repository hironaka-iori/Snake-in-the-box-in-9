import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec50 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1601 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1055 = true := by
  have hs : count1055 q = (countLit q [-89, -90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-91, -94])
  have hm := merge_left (literal (valuationOf q) (1051)) (literal (valuationOf q) (1055)) (countLit q [-89, -90]) (countLit q [-91, -94]) (count1055 q) 1 (meaning1051 q) (meaning1055 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1601 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1055 = true := counterClause1601 (baseVal q)

theorem counterClause1602 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1056 = true := by
  have hs : count1055 q = (countLit q [-89, -90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-91, -94])
  have hm := merge_two (literal (valuationOf q) (1051)) (literal (valuationOf q) (1053)) (literal (valuationOf q) (1056)) (countLit q [-89, -90]) (countLit q [-91, -94]) (count1055 q) 1 1 (meaning1051 q) (meaning1053 q) (meaning1056 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1602 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1053 = false ∨ valuation q 1056 = true := counterClause1602 (baseVal q)

theorem counterClause1603 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1057 = true := by
  have hs : count1055 q = (countLit q [-89, -90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-91, -94])
  have hm := merge_two (literal (valuationOf q) (1051)) (literal (valuationOf q) (1054)) (literal (valuationOf q) (1057)) (countLit q [-89, -90]) (countLit q [-91, -94]) (count1055 q) 1 2 (meaning1051 q) (meaning1054 q) (meaning1057 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1603 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1054 = false ∨ valuation q 1057 = true := counterClause1603 (baseVal q)

theorem counterClause1604 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1056 = true := by
  have hs : count1055 q = (countLit q [-89, -90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-91, -94])
  have hm := merge_left (literal (valuationOf q) (1052)) (literal (valuationOf q) (1056)) (countLit q [-89, -90]) (countLit q [-91, -94]) (count1055 q) 2 (meaning1052 q) (meaning1056 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1604 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1056 = true := counterClause1604 (baseVal q)

theorem counterClause1605 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1057 = true := by
  have hs : count1055 q = (countLit q [-89, -90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-91, -94])
  have hm := merge_two (literal (valuationOf q) (1052)) (literal (valuationOf q) (1053)) (literal (valuationOf q) (1057)) (countLit q [-89, -90]) (countLit q [-91, -94]) (count1055 q) 2 1 (meaning1052 q) (meaning1053 q) (meaning1057 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1605 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1053 = false ∨ valuation q 1057 = true := counterClause1605 (baseVal q)

theorem counterClause1606 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1058 = true := by
  have hs : count1055 q = (countLit q [-89, -90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-91, -94])
  have hm := merge_two (literal (valuationOf q) (1052)) (literal (valuationOf q) (1054)) (literal (valuationOf q) (1058)) (countLit q [-89, -90]) (countLit q [-91, -94]) (count1055 q) 2 2 (meaning1052 q) (meaning1054 q) (meaning1058 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1606 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1054 = false ∨ valuation q 1058 = true := counterClause1606 (baseVal q)

theorem counterClause1607 (q : Nat → Bool) : valuationOf q 1055 = false ∨ valuationOf q 1059 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_right (literal (valuationOf q) (1055)) (literal (valuationOf q) (1059)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 1 (meaning1055 q) (meaning1059 q) hs
  change valuationOf q 1055 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1607 (q : Snake 81) (h : Conditions q) : valuation q 1055 = false ∨ valuation q 1059 = true := counterClause1607 (baseVal q)

theorem counterClause1608 (q : Nat → Bool) : valuationOf q 1056 = false ∨ valuationOf q 1060 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_right (literal (valuationOf q) (1056)) (literal (valuationOf q) (1060)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 2 (meaning1056 q) (meaning1060 q) hs
  change valuationOf q 1056 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1608 (q : Snake 81) (h : Conditions q) : valuation q 1056 = false ∨ valuation q 1060 = true := counterClause1608 (baseVal q)

theorem counterClause1609 (q : Nat → Bool) : valuationOf q 1057 = false ∨ valuationOf q 1061 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_right (literal (valuationOf q) (1057)) (literal (valuationOf q) (1061)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 3 (meaning1057 q) (meaning1061 q) hs
  change valuationOf q 1057 = false ∨ valuationOf q 1061 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1609 (q : Snake 81) (h : Conditions q) : valuation q 1057 = false ∨ valuation q 1061 = true := counterClause1609 (baseVal q)

theorem counterClause1610 (q : Nat → Bool) : valuationOf q 1058 = false ∨ valuationOf q 1062 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_right (literal (valuationOf q) (1058)) (literal (valuationOf q) (1062)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 4 (meaning1058 q) (meaning1062 q) hs
  change valuationOf q 1058 = false ∨ valuationOf q 1062 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1610 (q : Snake 81) (h : Conditions q) : valuation q 1058 = false ∨ valuation q 1062 = true := counterClause1610 (baseVal q)

theorem counterClause1611 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1059 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_left (literal (valuationOf q) (1047)) (literal (valuationOf q) (1059)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 1 (meaning1047 q) (meaning1059 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1611 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1059 = true := counterClause1611 (baseVal q)

theorem counterClause1612 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1060 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1055)) (literal (valuationOf q) (1060)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 1 1 (meaning1047 q) (meaning1055 q) (meaning1060 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1612 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1055 = false ∨ valuation q 1060 = true := counterClause1612 (baseVal q)

theorem counterClause1613 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1061 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1061)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 1 2 (meaning1047 q) (meaning1056 q) (meaning1061 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1061 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1613 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1056 = false ∨ valuation q 1061 = true := counterClause1613 (baseVal q)

theorem counterClause1614 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1062 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1062)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 1 3 (meaning1047 q) (meaning1057 q) (meaning1062 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1062 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1614 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1057 = false ∨ valuation q 1062 = true := counterClause1614 (baseVal q)

theorem counterClause1615 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1063 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1063)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 1 4 (meaning1047 q) (meaning1058 q) (meaning1063 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1063 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1615 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1058 = false ∨ valuation q 1063 = true := counterClause1615 (baseVal q)

theorem counterClause1616 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1060 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_left (literal (valuationOf q) (1048)) (literal (valuationOf q) (1060)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 2 (meaning1048 q) (meaning1060 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1616 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1060 = true := counterClause1616 (baseVal q)

theorem counterClause1617 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1061 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1055)) (literal (valuationOf q) (1061)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 2 1 (meaning1048 q) (meaning1055 q) (meaning1061 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1061 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1617 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1055 = false ∨ valuation q 1061 = true := counterClause1617 (baseVal q)

theorem counterClause1618 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1062 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1062)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 2 2 (meaning1048 q) (meaning1056 q) (meaning1062 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1062 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1618 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1056 = false ∨ valuation q 1062 = true := counterClause1618 (baseVal q)

theorem counterClause1619 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1063 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1063)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 2 3 (meaning1048 q) (meaning1057 q) (meaning1063 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1063 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1619 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1057 = false ∨ valuation q 1063 = true := counterClause1619 (baseVal q)

theorem counterClause1620 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1064 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1064)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 2 4 (meaning1048 q) (meaning1058 q) (meaning1064 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1064 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1620 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1058 = false ∨ valuation q 1064 = true := counterClause1620 (baseVal q)

theorem counterClause1621 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1061 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_left (literal (valuationOf q) (1049)) (literal (valuationOf q) (1061)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 3 (meaning1049 q) (meaning1061 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1061 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1621 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1061 = true := counterClause1621 (baseVal q)

theorem counterClause1622 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1062 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1049)) (literal (valuationOf q) (1055)) (literal (valuationOf q) (1062)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 3 1 (meaning1049 q) (meaning1055 q) (meaning1062 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1062 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1622 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1055 = false ∨ valuation q 1062 = true := counterClause1622 (baseVal q)

theorem counterClause1623 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1063 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1049)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1063)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 3 2 (meaning1049 q) (meaning1056 q) (meaning1063 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1063 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1623 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1056 = false ∨ valuation q 1063 = true := counterClause1623 (baseVal q)

theorem counterClause1624 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1064 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1049)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1064)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 3 3 (meaning1049 q) (meaning1057 q) (meaning1064 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1064 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1624 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1057 = false ∨ valuation q 1064 = true := counterClause1624 (baseVal q)

theorem counterClause1625 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1065 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1049)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1065)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 3 4 (meaning1049 q) (meaning1058 q) (meaning1065 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1065 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1625 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1058 = false ∨ valuation q 1065 = true := counterClause1625 (baseVal q)

theorem counterClause1626 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1062 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_left (literal (valuationOf q) (1050)) (literal (valuationOf q) (1062)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 4 (meaning1050 q) (meaning1062 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1062 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1626 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1062 = true := counterClause1626 (baseVal q)

theorem counterClause1627 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1063 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1050)) (literal (valuationOf q) (1055)) (literal (valuationOf q) (1063)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 4 1 (meaning1050 q) (meaning1055 q) (meaning1063 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1063 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1627 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1055 = false ∨ valuation q 1063 = true := counterClause1627 (baseVal q)

theorem counterClause1628 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1064 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1050)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1064)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 4 2 (meaning1050 q) (meaning1056 q) (meaning1064 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1064 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1628 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1056 = false ∨ valuation q 1064 = true := counterClause1628 (baseVal q)

theorem counterClause1629 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1065 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1050)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1065)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 4 3 (meaning1050 q) (meaning1057 q) (meaning1065 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1065 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1629 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1057 = false ∨ valuation q 1065 = true := counterClause1629 (baseVal q)

theorem counterClause1630 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1066 = true := by
  have hs : count1059 q = (countLit q [-82, -83, -86, -87]) + (countLit q [-89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -86, -87]) (l₂ := [-89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1050)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1066)) (countLit q [-82, -83, -86, -87]) (countLit q [-89, -90, -91, -94]) (count1059 q) 4 4 (meaning1050 q) (meaning1058 q) (meaning1066 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1630 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1058 = false ∨ valuation q 1066 = true := counterClause1630 (baseVal q)

theorem counterClause1631 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1073 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1063)) (literal (valuationOf q) (1073)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 2 5 (meaning1036 q) (meaning1063 q) (meaning1073 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1073 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1631 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1063 = false ∨ valuation q 1073 = true := counterClause1631 (baseVal q)

theorem counterClause1632 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1064 = false ∨ valuationOf q 1074 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1064)) (literal (valuationOf q) (1074)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 2 6 (meaning1036 q) (meaning1064 q) (meaning1074 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1064 = false ∨ valuationOf q 1074 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1632 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1064 = false ∨ valuation q 1074 = true := counterClause1632 (baseVal q)

theorem block50 (q : Snake 81) (h : Conditions q) : B112E057.Block50 (valuation q) :=
  ⟨clause1601 q h, clause1602 q h, clause1603 q h, clause1604 q h, clause1605 q h, clause1606 q h, clause1607 q h, clause1608 q h, clause1609 q h, clause1610 q h, clause1611 q h, clause1612 q h, clause1613 q h, clause1614 q h, clause1615 q h, clause1616 q h, clause1617 q h, clause1618 q h, clause1619 q h, clause1620 q h, clause1621 q h, clause1622 q h, clause1623 q h, clause1624 q h, clause1625 q h, clause1626 q h, clause1627 q h, clause1628 q h, clause1629 q h, clause1630 q h, clause1631 q h, clause1632 q h⟩

end
end Snake9.Regrowth.E112057
