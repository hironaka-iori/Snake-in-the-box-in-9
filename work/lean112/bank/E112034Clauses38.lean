import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-36, -37]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1618)) (countLit q [-36, -37]) (countLit q [-40, -42]) (count1616 q) 2 1 (meaning1613 q) (meaning1614 q) (meaning1618 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1614 = false ∨ valuation q 1618 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-36, -37]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1619)) (countLit q [-36, -37]) (countLit q [-40, -42]) (count1616 q) 2 2 (meaning1613 q) (meaning1615 q) (meaning1619 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1615 = false ∨ valuation q 1619 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1620 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1616)) (literal (valuationOf q) (1620)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 1 (meaning1616 q) (meaning1620 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1620 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1621 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1617)) (literal (valuationOf q) (1621)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 2 (meaning1617 q) (meaning1621 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1621 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1622 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1618)) (literal (valuationOf q) (1622)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 3 (meaning1618 q) (meaning1622 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1622 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1623 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1619)) (literal (valuationOf q) (1623)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 4 (meaning1619 q) (meaning1623 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1623 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1620 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1608)) (literal (valuationOf q) (1620)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 1 (meaning1608 q) (meaning1620 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1620 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1621 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1621)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 1 1 (meaning1608 q) (meaning1616 q) (meaning1621 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1616 = false ∨ valuation q 1621 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1622 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1622)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 1 2 (meaning1608 q) (meaning1617 q) (meaning1622 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1617 = false ∨ valuation q 1622 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1623 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1623)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 1 3 (meaning1608 q) (meaning1618 q) (meaning1623 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1618 = false ∨ valuation q 1623 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1624 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1624)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 1 4 (meaning1608 q) (meaning1619 q) (meaning1624 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1619 = false ∨ valuation q 1624 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1621 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1609)) (literal (valuationOf q) (1621)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 2 (meaning1609 q) (meaning1621 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1621 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1622 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1622)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 2 1 (meaning1609 q) (meaning1616 q) (meaning1622 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1616 = false ∨ valuation q 1622 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1623 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1623)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 2 2 (meaning1609 q) (meaning1617 q) (meaning1623 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1617 = false ∨ valuation q 1623 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1624 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1624)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 2 3 (meaning1609 q) (meaning1618 q) (meaning1624 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1618 = false ∨ valuation q 1624 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1625 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1625)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 2 4 (meaning1609 q) (meaning1619 q) (meaning1625 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1619 = false ∨ valuation q 1625 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1622 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1610)) (literal (valuationOf q) (1622)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 3 (meaning1610 q) (meaning1622 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1622 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1623 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1623)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 3 1 (meaning1610 q) (meaning1616 q) (meaning1623 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1616 = false ∨ valuation q 1623 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1624 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1624)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 3 2 (meaning1610 q) (meaning1617 q) (meaning1624 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1617 = false ∨ valuation q 1624 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1625 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1625)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 3 3 (meaning1610 q) (meaning1618 q) (meaning1625 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1618 = false ∨ valuation q 1625 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1624 = true := by
  have hs : count1620 q = (countLit q [-28, -29, -33, -35]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1624)) (countLit q [-28, -29, -33, -35]) (countLit q [-36, -37, -40, -42]) (count1620 q) 4 1 (meaning1611 q) (meaning1616 q) (meaning1624 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1616 = false ∨ valuation q 1624 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1628 = true := by
  have hs : count1628 q = (countLit q [-44]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1628)) (countLit q [-44]) (countLit q [-46]) (count1628 q) 1 (meaningNeg46 q) (meaning1628 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1628 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1628 = true := by
  have hs : count1628 q = (countLit q [-44]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1628)) (countLit q [-44]) (countLit q [-46]) (count1628 q) 1 (meaningNeg44 q) (meaning1628 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1628 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 46 = true ∨ valuationOf q 1629 = true := by
  have hs : count1628 q = (countLit q [-44]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (1629)) (countLit q [-44]) (countLit q [-46]) (count1628 q) 1 1 (meaningNeg44 q) (meaningNeg46 q) (meaning1629 q) hs
  change (! (valuationOf q 44)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 46 = true ∨ valuation q 1629 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1630)) (countLit q [-48]) (countLit q [-51]) (count1630 q) 1 (meaningNeg51 q) (meaning1630 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1630 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1630)) (countLit q [-48]) (countLit q [-51]) (count1630 q) 1 (meaningNeg48 q) (meaning1630 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1630 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1631 = true := by
  have hs : count1630 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1631)) (countLit q [-48]) (countLit q [-51]) (count1630 q) 1 1 (meaningNeg48 q) (meaningNeg51 q) (meaning1631 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 51 = true ∨ valuation q 1631 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-44, -46]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-48, -51])
  have hm := merge_right (literal (valuationOf q) (1630)) (literal (valuationOf q) (1632)) (countLit q [-44, -46]) (countLit q [-48, -51]) (count1632 q) 1 (meaning1630 q) (meaning1632 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1632 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-44, -46]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-48, -51])
  have hm := merge_right (literal (valuationOf q) (1631)) (literal (valuationOf q) (1633)) (countLit q [-44, -46]) (countLit q [-48, -51]) (count1632 q) 2 (meaning1631 q) (meaning1633 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1633 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-44, -46]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-48, -51])
  have hm := merge_left (literal (valuationOf q) (1628)) (literal (valuationOf q) (1632)) (countLit q [-44, -46]) (countLit q [-48, -51]) (count1632 q) 1 (meaning1628 q) (meaning1632 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1632 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-44, -46]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-48, -51])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1633)) (countLit q [-44, -46]) (countLit q [-48, -51]) (count1632 q) 1 1 (meaning1628 q) (meaning1630 q) (meaning1633 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1630 = false ∨ valuation q 1633 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1634 = true := by
  have hs : count1632 q = (countLit q [-44, -46]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-48, -51])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1634)) (countLit q [-44, -46]) (countLit q [-48, -51]) (count1632 q) 1 2 (meaning1628 q) (meaning1631 q) (meaning1634 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1631 = false ∨ valuation q 1634 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E034.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112034
