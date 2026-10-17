import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1620 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1620)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 7 2 (meaning1586 q) (meaning1605 q) (meaning1620 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1605 = false ∨ valuation q 1620 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1635 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1635)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 4 4 (meaning1552 q) (meaning1615 q) (meaning1635 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1615 = false ∨ valuation q 1635 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1636 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1636)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 4 5 (meaning1552 q) (meaning1616 q) (meaning1636 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1616 = false ∨ valuation q 1636 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1635 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1635)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 5 3 (meaning1553 q) (meaning1614 q) (meaning1635 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1614 = false ∨ valuation q 1635 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1636 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1636)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 5 4 (meaning1553 q) (meaning1615 q) (meaning1636 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1615 = false ∨ valuation q 1636 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1637 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1637)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 5 5 (meaning1553 q) (meaning1616 q) (meaning1637 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1616 = false ∨ valuation q 1637 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1638 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1638)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 5 6 (meaning1553 q) (meaning1617 q) (meaning1638 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1617 = false ∨ valuation q 1638 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1639 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1639)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 5 7 (meaning1553 q) (meaning1618 q) (meaning1639 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1618 = false ∨ valuation q 1639 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1640 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1640)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 5 8 (meaning1553 q) (meaning1619 q) (meaning1640 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1619 = false ∨ valuation q 1640 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1641 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1641)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 5 9 (meaning1553 q) (meaning1620 q) (meaning1641 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1620 = false ∨ valuation q 1641 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1642 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1642)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 5 10 (meaning1553 q) (meaning1621 q) (meaning1642 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1621 = false ∨ valuation q 1642 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1636 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1636)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 6 3 (meaning1554 q) (meaning1614 q) (meaning1636 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1614 = false ∨ valuation q 1636 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1637 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1637)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 6 4 (meaning1554 q) (meaning1615 q) (meaning1637 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1615 = false ∨ valuation q 1637 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1638 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1638)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 6 5 (meaning1554 q) (meaning1616 q) (meaning1638 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1616 = false ∨ valuation q 1638 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1639 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1639)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 6 6 (meaning1554 q) (meaning1617 q) (meaning1639 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1617 = false ∨ valuation q 1639 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1640 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1640)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 6 7 (meaning1554 q) (meaning1618 q) (meaning1640 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1618 = false ∨ valuation q 1640 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1641 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1641)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 6 8 (meaning1554 q) (meaning1619 q) (meaning1641 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1619 = false ∨ valuation q 1641 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1642 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1642)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 6 9 (meaning1554 q) (meaning1620 q) (meaning1642 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1620 = false ∨ valuation q 1642 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1637 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1637)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 7 3 (meaning1555 q) (meaning1614 q) (meaning1637 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1614 = false ∨ valuation q 1637 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1638 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1638)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 7 4 (meaning1555 q) (meaning1615 q) (meaning1638 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1615 = false ∨ valuation q 1638 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1639 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1639)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 7 5 (meaning1555 q) (meaning1616 q) (meaning1639 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1616 = false ∨ valuation q 1639 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1640 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1640)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 7 6 (meaning1555 q) (meaning1617 q) (meaning1640 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1617 = false ∨ valuation q 1640 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1641 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1641)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 7 7 (meaning1555 q) (meaning1618 q) (meaning1641 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1618 = false ∨ valuation q 1641 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1642 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1642)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 7 8 (meaning1555 q) (meaning1619 q) (meaning1642 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1619 = false ∨ valuation q 1642 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1637 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1637)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 8 2 (meaning1556 q) (meaning1613 q) (meaning1637 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1613 = false ∨ valuation q 1637 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1638 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1638)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 8 3 (meaning1556 q) (meaning1614 q) (meaning1638 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1614 = false ∨ valuation q 1638 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1639 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1639)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 8 4 (meaning1556 q) (meaning1615 q) (meaning1639 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1615 = false ∨ valuation q 1639 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1640 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1640)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 8 5 (meaning1556 q) (meaning1616 q) (meaning1640 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1616 = false ∨ valuation q 1640 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1641 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1641)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 8 6 (meaning1556 q) (meaning1617 q) (meaning1641 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1617 = false ∨ valuation q 1641 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1642 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1642)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 8 7 (meaning1556 q) (meaning1618 q) (meaning1642 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1618 = false ∨ valuation q 1642 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1638 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1638)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 9 2 (meaning1557 q) (meaning1613 q) (meaning1638 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1613 = false ∨ valuation q 1638 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1639 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1639)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 9 3 (meaning1557 q) (meaning1614 q) (meaning1639 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1614 = false ∨ valuation q 1639 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E008.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112008
