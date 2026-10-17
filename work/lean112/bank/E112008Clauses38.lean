import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1615 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1615)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 1 3 (meaning1580 q) (meaning1606 q) (meaning1615 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1606 = false ∨ valuation q 1615 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1616 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1616)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 1 4 (meaning1580 q) (meaning1607 q) (meaning1616 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1607 = false ∨ valuation q 1616 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1617 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1617)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 1 5 (meaning1580 q) (meaning1608 q) (meaning1617 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1608 = false ∨ valuation q 1617 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1618 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1618)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 1 6 (meaning1580 q) (meaning1609 q) (meaning1618 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1609 = false ∨ valuation q 1618 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1614)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 2 1 (meaning1581 q) (meaning1604 q) (meaning1614 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1604 = false ∨ valuation q 1614 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1615 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1615)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 2 2 (meaning1581 q) (meaning1605 q) (meaning1615 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1605 = false ∨ valuation q 1615 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1616 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1616)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 2 3 (meaning1581 q) (meaning1606 q) (meaning1616 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1606 = false ∨ valuation q 1616 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1617 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1617)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 2 4 (meaning1581 q) (meaning1607 q) (meaning1617 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1607 = false ∨ valuation q 1617 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1618 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1618)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 2 5 (meaning1581 q) (meaning1608 q) (meaning1618 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1608 = false ∨ valuation q 1618 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1619 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1619)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 2 6 (meaning1581 q) (meaning1609 q) (meaning1619 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1609 = false ∨ valuation q 1619 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1620 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1620)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 2 7 (meaning1581 q) (meaning1610 q) (meaning1620 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1610 = false ∨ valuation q 1620 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1582)) (literal (valuationOf q) (1614)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 3 (meaning1582 q) (meaning1614 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1614 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1615 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1615)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 3 1 (meaning1582 q) (meaning1604 q) (meaning1615 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1604 = false ∨ valuation q 1615 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1616 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1616)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 3 2 (meaning1582 q) (meaning1605 q) (meaning1616 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1605 = false ∨ valuation q 1616 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1617 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1617)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 3 3 (meaning1582 q) (meaning1606 q) (meaning1617 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1606 = false ∨ valuation q 1617 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1618 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1618)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 3 4 (meaning1582 q) (meaning1607 q) (meaning1618 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1607 = false ∨ valuation q 1618 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1619 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1619)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 3 5 (meaning1582 q) (meaning1608 q) (meaning1619 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1608 = false ∨ valuation q 1619 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1620 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1620)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 3 6 (meaning1582 q) (meaning1609 q) (meaning1620 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1609 = false ∨ valuation q 1620 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1616 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1616)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 4 1 (meaning1583 q) (meaning1604 q) (meaning1616 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1604 = false ∨ valuation q 1616 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1617 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1617)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 4 2 (meaning1583 q) (meaning1605 q) (meaning1617 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1605 = false ∨ valuation q 1617 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1618 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1618)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 4 3 (meaning1583 q) (meaning1606 q) (meaning1618 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1606 = false ∨ valuation q 1618 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1619 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1619)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 4 4 (meaning1583 q) (meaning1607 q) (meaning1619 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1607 = false ∨ valuation q 1619 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1620 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1620)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 4 5 (meaning1583 q) (meaning1608 q) (meaning1620 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1608 = false ∨ valuation q 1620 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1617 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1617)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 5 1 (meaning1584 q) (meaning1604 q) (meaning1617 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1604 = false ∨ valuation q 1617 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1618 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1618)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 5 2 (meaning1584 q) (meaning1605 q) (meaning1618 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1605 = false ∨ valuation q 1618 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1619 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1619)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 5 3 (meaning1584 q) (meaning1606 q) (meaning1619 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1606 = false ∨ valuation q 1619 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1620 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1620)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 5 4 (meaning1584 q) (meaning1607 q) (meaning1620 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1607 = false ∨ valuation q 1620 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1621 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1621)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 5 5 (meaning1584 q) (meaning1608 q) (meaning1621 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1608 = false ∨ valuation q 1621 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1618 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1618)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 6 1 (meaning1585 q) (meaning1604 q) (meaning1618 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1604 = false ∨ valuation q 1618 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1619 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1619)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 6 2 (meaning1585 q) (meaning1605 q) (meaning1619 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1605 = false ∨ valuation q 1619 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1620 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1620)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 6 3 (meaning1585 q) (meaning1606 q) (meaning1620 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1606 = false ∨ valuation q 1620 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1619 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1619)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 7 1 (meaning1586 q) (meaning1604 q) (meaning1619 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1604 = false ∨ valuation q 1619 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E008.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112008
