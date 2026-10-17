import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1512 = true := by
  have hs : count1511 q = (countLit q [-33]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1512)) (countLit q [-33]) (countLit q [-37]) (count1511 q) 1 1 (meaningNeg33 q) (meaningNeg37 q) (meaning1512 q) hs
  change (! (valuationOf q 33)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 37 = true ∨ valuation q 1512 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1513 = true := by
  have hs : count1513 q = (countLit q [-30]) + (countLit q [-33, -37]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33, -37])
  have hm := merge_right (literal (valuationOf q) (1511)) (literal (valuationOf q) (1513)) (countLit q [-30]) (countLit q [-33, -37]) (count1513 q) 1 (meaning1511 q) (meaning1513 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1513 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-30]) + (countLit q [-33, -37]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33, -37])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1514)) (countLit q [-30]) (countLit q [-33, -37]) (count1513 q) 2 (meaning1512 q) (meaning1514 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1514 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1513 = true := by
  have hs : count1513 q = (countLit q [-30]) + (countLit q [-33, -37]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33, -37])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1513)) (countLit q [-30]) (countLit q [-33, -37]) (count1513 q) 1 (meaningNeg30 q) (meaning1513 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1513 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1511 = false ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-30]) + (countLit q [-33, -37]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33, -37])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1514)) (countLit q [-30]) (countLit q [-33, -37]) (count1513 q) 1 1 (meaningNeg30 q) (meaning1511 q) (meaning1514 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1511 = false ∨ valuation q 1514 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1516 = true := by
  have hs : count1516 q = (countLit q [-38]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (1516)) (countLit q [-38]) (countLit q [-39]) (count1516 q) 1 (meaningNeg39 q) (meaning1516 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1516 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1516 = true := by
  have hs : count1516 q = (countLit q [-38]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1516)) (countLit q [-38]) (countLit q [-39]) (count1516 q) 1 (meaningNeg38 q) (meaning1516 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1516 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 39 = true ∨ valuationOf q 1517 = true := by
  have hs : count1516 q = (countLit q [-38]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-39])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (-39)) (literal (valuationOf q) (1517)) (countLit q [-38]) (countLit q [-39]) (count1516 q) 1 1 (meaningNeg38 q) (meaningNeg39 q) (meaning1517 q) hs
  change (! (valuationOf q 38)) = false ∨ (! (valuationOf q 39)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 39 = true ∨ valuation q 1517 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-40]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1518)) (countLit q [-40]) (countLit q [-44]) (count1518 q) 1 (meaningNeg44 q) (meaning1518 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1518 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-40]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1518)) (countLit q [-40]) (countLit q [-44]) (count1518 q) 1 (meaningNeg40 q) (meaning1518 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1518 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-40]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1519)) (countLit q [-40]) (countLit q [-44]) (count1518 q) 1 1 (meaningNeg40 q) (meaningNeg44 q) (meaning1519 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 44 = true ∨ valuation q 1519 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1520 = true := by
  have hs : count1520 q = (countLit q [-38, -39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-40, -44])
  have hm := merge_right (literal (valuationOf q) (1518)) (literal (valuationOf q) (1520)) (countLit q [-38, -39]) (countLit q [-40, -44]) (count1520 q) 1 (meaning1518 q) (meaning1520 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1520 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1521 = true := by
  have hs : count1520 q = (countLit q [-38, -39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-40, -44])
  have hm := merge_right (literal (valuationOf q) (1519)) (literal (valuationOf q) (1521)) (countLit q [-38, -39]) (countLit q [-40, -44]) (count1520 q) 2 (meaning1519 q) (meaning1521 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1521 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1520 = true := by
  have hs : count1520 q = (countLit q [-38, -39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-40, -44])
  have hm := merge_left (literal (valuationOf q) (1516)) (literal (valuationOf q) (1520)) (countLit q [-38, -39]) (countLit q [-40, -44]) (count1520 q) 1 (meaning1516 q) (meaning1520 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1520 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1521 = true := by
  have hs : count1520 q = (countLit q [-38, -39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-40, -44])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1521)) (countLit q [-38, -39]) (countLit q [-40, -44]) (count1520 q) 1 1 (meaning1516 q) (meaning1518 q) (meaning1521 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1518 = false ∨ valuation q 1521 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1522 = true := by
  have hs : count1520 q = (countLit q [-38, -39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-40, -44])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1522)) (countLit q [-38, -39]) (countLit q [-40, -44]) (count1520 q) 1 2 (meaning1516 q) (meaning1519 q) (meaning1522 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1519 = false ∨ valuation q 1522 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1522 = true := by
  have hs : count1520 q = (countLit q [-38, -39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-40, -44])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1522)) (countLit q [-38, -39]) (countLit q [-40, -44]) (count1520 q) 2 1 (meaning1517 q) (meaning1518 q) (meaning1522 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1518 = false ∨ valuation q 1522 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-30, -33, -37]) + (countLit q [-38, -39, -40, -44]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37]) (l₂ := [-38, -39, -40, -44])
  have hm := merge_right (literal (valuationOf q) (1520)) (literal (valuationOf q) (1524)) (countLit q [-30, -33, -37]) (countLit q [-38, -39, -40, -44]) (count1524 q) 1 (meaning1520 q) (meaning1524 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1524 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-30, -33, -37]) + (countLit q [-38, -39, -40, -44]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37]) (l₂ := [-38, -39, -40, -44])
  have hm := merge_right (literal (valuationOf q) (1521)) (literal (valuationOf q) (1525)) (countLit q [-30, -33, -37]) (countLit q [-38, -39, -40, -44]) (count1524 q) 2 (meaning1521 q) (meaning1525 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1525 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1526 = true := by
  have hs : count1524 q = (countLit q [-30, -33, -37]) + (countLit q [-38, -39, -40, -44]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37]) (l₂ := [-38, -39, -40, -44])
  have hm := merge_right (literal (valuationOf q) (1522)) (literal (valuationOf q) (1526)) (countLit q [-30, -33, -37]) (countLit q [-38, -39, -40, -44]) (count1524 q) 3 (meaning1522 q) (meaning1526 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1526 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-30, -33, -37]) + (countLit q [-38, -39, -40, -44]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37]) (l₂ := [-38, -39, -40, -44])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1525)) (countLit q [-30, -33, -37]) (countLit q [-38, -39, -40, -44]) (count1524 q) 1 1 (meaning1513 q) (meaning1520 q) (meaning1525 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1520 = false ∨ valuation q 1525 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1526 = true := by
  have hs : count1524 q = (countLit q [-30, -33, -37]) + (countLit q [-38, -39, -40, -44]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37]) (l₂ := [-38, -39, -40, -44])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1526)) (countLit q [-30, -33, -37]) (countLit q [-38, -39, -40, -44]) (count1524 q) 1 2 (meaning1513 q) (meaning1521 q) (meaning1526 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1521 = false ∨ valuation q 1526 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1526 = true := by
  have hs : count1524 q = (countLit q [-30, -33, -37]) + (countLit q [-38, -39, -40, -44]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37]) (l₂ := [-38, -39, -40, -44])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1526)) (countLit q [-30, -33, -37]) (countLit q [-38, -39, -40, -44]) (count1524 q) 2 1 (meaning1514 q) (meaning1520 q) (meaning1526 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1520 = false ∨ valuation q 1526 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1527 = true := by
  have hs : count1524 q = (countLit q [-30, -33, -37]) + (countLit q [-38, -39, -40, -44]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37]) (l₂ := [-38, -39, -40, -44])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1527)) (countLit q [-30, -33, -37]) (countLit q [-38, -39, -40, -44]) (count1524 q) 2 2 (meaning1514 q) (meaning1521 q) (meaning1527 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1521 = false ∨ valuation q 1527 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1531)) (countLit q [-46]) (countLit q [-47]) (count1531 q) 1 (meaningNeg47 q) (meaning1531 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1531 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1531)) (countLit q [-46]) (countLit q [-47]) (count1531 q) 1 (meaningNeg46 q) (meaning1531 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1531 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 47 = true ∨ valuationOf q 1532 = true := by
  have hs : count1531 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (1532)) (countLit q [-46]) (countLit q [-47]) (count1531 q) 1 1 (meaningNeg46 q) (meaningNeg47 q) (meaning1532 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 47 = true ∨ valuation q 1532 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (1533)) (countLit q [-48]) (countLit q [-50]) (count1533 q) 1 (meaningNeg50 q) (meaning1533 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1533 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1533)) (countLit q [-48]) (countLit q [-50]) (count1533 q) 1 (meaningNeg48 q) (meaning1533 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1533 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 50 = true ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-50)) (literal (valuationOf q) (1534)) (countLit q [-48]) (countLit q [-50]) (count1533 q) 1 1 (meaningNeg48 q) (meaningNeg50 q) (meaning1534 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 50)) = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 50 = true ∨ valuation q 1534 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_right (literal (valuationOf q) (1533)) (literal (valuationOf q) (1535)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1535 q) 1 (meaning1533 q) (meaning1535 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1535 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_right (literal (valuationOf q) (1534)) (literal (valuationOf q) (1536)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1535 q) 2 (meaning1534 q) (meaning1536 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1536 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E152.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112152
