import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-103, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1606)) (countLit q [-103, -104]) (countLit q [-106, -107]) (count1604 q) 2 1 (meaning1601 q) (meaning1602 q) (meaning1606 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1602 = false ∨ valuation q 1606 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_right (literal (valuationOf q) (-112)) (literal (valuationOf q) (1608)) (countLit q [-111]) (countLit q [-112]) (count1608 q) 1 (meaningNeg112 q) (meaning1608 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1608 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1608)) (countLit q [-111]) (countLit q [-112]) (count1608 q) 1 (meaningNeg111 q) (meaning1608 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1608 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 112 = true ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-112)) (literal (valuationOf q) (1609)) (countLit q [-111]) (countLit q [-112]) (count1608 q) 1 1 (meaningNeg111 q) (meaningNeg112 q) (meaning1609 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 112)) = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 1609 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_right (literal (valuationOf q) (-114)) (literal (valuationOf q) (1610)) (countLit q [-113]) (countLit q [-114]) (count1610 q) 1 (meaningNeg114 q) (meaning1610 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1610 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_left (literal (valuationOf q) (-113)) (literal (valuationOf q) (1610)) (countLit q [-113]) (countLit q [-114]) (count1610 q) 1 (meaningNeg113 q) (meaning1610 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1610 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 114 = true ∨ valuationOf q 1611 = true := by
  have hs : count1610 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_two (literal (valuationOf q) (-113)) (literal (valuationOf q) (-114)) (literal (valuationOf q) (1611)) (countLit q [-113]) (countLit q [-114]) (count1610 q) 1 1 (meaningNeg113 q) (meaningNeg114 q) (meaning1611 q) hs
  change (! (valuationOf q 113)) = false ∨ (! (valuationOf q 114)) = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 1611 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_right (literal (valuationOf q) (1610)) (literal (valuationOf q) (1612)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count1612 q) 1 (meaning1610 q) (meaning1612 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1612 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_right (literal (valuationOf q) (1611)) (literal (valuationOf q) (1613)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count1612 q) 2 (meaning1611 q) (meaning1613 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1613 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_left (literal (valuationOf q) (1608)) (literal (valuationOf q) (1612)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count1612 q) 1 (meaning1608 q) (meaning1612 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1612 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1613)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count1612 q) 1 1 (meaning1608 q) (meaning1610 q) (meaning1613 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1610 = false ∨ valuation q 1613 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_left (literal (valuationOf q) (1609)) (literal (valuationOf q) (1613)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count1612 q) 2 (meaning1609 q) (meaning1613 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1613 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-103, -104, -106, -107]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -106, -107]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_right (literal (valuationOf q) (1612)) (literal (valuationOf q) (1616)) (countLit q [-103, -104, -106, -107]) (countLit q [-111, -112, -113, -114]) (count1616 q) 1 (meaning1612 q) (meaning1616 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1616 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-103, -104, -106, -107]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -106, -107]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1617)) (countLit q [-103, -104, -106, -107]) (countLit q [-111, -112, -113, -114]) (count1616 q) 1 1 (meaning1604 q) (meaning1612 q) (meaning1617 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1612 = false ∨ valuation q 1617 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-103, -104, -106, -107]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -106, -107]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1618)) (countLit q [-103, -104, -106, -107]) (countLit q [-111, -112, -113, -114]) (count1616 q) 1 2 (meaning1604 q) (meaning1613 q) (meaning1618 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1613 = false ∨ valuation q 1618 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-103, -104, -106, -107]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -106, -107]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1618)) (countLit q [-103, -104, -106, -107]) (countLit q [-111, -112, -113, -114]) (count1616 q) 2 1 (meaning1605 q) (meaning1612 q) (meaning1618 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1612 = false ∨ valuation q 1618 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-103, -104, -106, -107]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -106, -107]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1619)) (countLit q [-103, -104, -106, -107]) (countLit q [-111, -112, -113, -114]) (count1616 q) 2 2 (meaning1605 q) (meaning1613 q) (meaning1619 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1613 = false ∨ valuation q 1619 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-103, -104, -106, -107]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -106, -107]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1619)) (countLit q [-103, -104, -106, -107]) (countLit q [-111, -112, -113, -114]) (count1616 q) 3 1 (meaning1606 q) (meaning1612 q) (meaning1619 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1612 = false ∨ valuation q 1619 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1620 = true := by
  have hs : count1616 q = (countLit q [-103, -104, -106, -107]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -106, -107]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1620)) (countLit q [-103, -104, -106, -107]) (countLit q [-111, -112, -113, -114]) (count1616 q) 3 2 (meaning1606 q) (meaning1613 q) (meaning1620 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1613 = false ∨ valuation q 1620 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1627 = true := by
  have hs : count1624 q = (countLit q [-88, -90, -94, -95, -96, -97, -101]) + (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -96, -97, -101]) (l₂ := [-103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_right (literal (valuationOf q) (1619)) (literal (valuationOf q) (1627)) (countLit q [-88, -90, -94, -95, -96, -97, -101]) (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) (count1624 q) 4 (meaning1619 q) (meaning1627 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1627 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1625 = true := by
  have hs : count1624 q = (countLit q [-88, -90, -94, -95, -96, -97, -101]) + (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -96, -97, -101]) (l₂ := [-103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1625)) (countLit q [-88, -90, -94, -95, -96, -97, -101]) (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) (count1624 q) 1 1 (meaning1593 q) (meaning1616 q) (meaning1625 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1616 = false ∨ valuation q 1625 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1626 = true := by
  have hs : count1624 q = (countLit q [-88, -90, -94, -95, -96, -97, -101]) + (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -96, -97, -101]) (l₂ := [-103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1626)) (countLit q [-88, -90, -94, -95, -96, -97, -101]) (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) (count1624 q) 1 2 (meaning1593 q) (meaning1617 q) (meaning1626 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1617 = false ∨ valuation q 1626 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1627 = true := by
  have hs : count1624 q = (countLit q [-88, -90, -94, -95, -96, -97, -101]) + (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -96, -97, -101]) (l₂ := [-103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1627)) (countLit q [-88, -90, -94, -95, -96, -97, -101]) (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) (count1624 q) 1 3 (meaning1593 q) (meaning1618 q) (meaning1627 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1618 = false ∨ valuation q 1627 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-88, -90, -94, -95, -96, -97, -101]) + (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -96, -97, -101]) (l₂ := [-103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1628)) (countLit q [-88, -90, -94, -95, -96, -97, -101]) (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) (count1624 q) 1 4 (meaning1593 q) (meaning1619 q) (meaning1628 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1619 = false ∨ valuation q 1628 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-88, -90, -94, -95, -96, -97, -101]) + (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -96, -97, -101]) (l₂ := [-103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1629)) (countLit q [-88, -90, -94, -95, -96, -97, -101]) (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) (count1624 q) 1 5 (meaning1593 q) (meaning1620 q) (meaning1629 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1620 = false ∨ valuation q 1629 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1627 = true := by
  have hs : count1624 q = (countLit q [-88, -90, -94, -95, -96, -97, -101]) + (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -96, -97, -101]) (l₂ := [-103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1627)) (countLit q [-88, -90, -94, -95, -96, -97, -101]) (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) (count1624 q) 2 2 (meaning1594 q) (meaning1617 q) (meaning1627 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1617 = false ∨ valuation q 1627 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-88, -90, -94, -95, -96, -97, -101]) + (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -96, -97, -101]) (l₂ := [-103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1628)) (countLit q [-88, -90, -94, -95, -96, -97, -101]) (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) (count1624 q) 2 3 (meaning1594 q) (meaning1618 q) (meaning1628 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1618 = false ∨ valuation q 1628 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-88, -90, -94, -95, -96, -97, -101]) + (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -96, -97, -101]) (l₂ := [-103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1629)) (countLit q [-88, -90, -94, -95, -96, -97, -101]) (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) (count1624 q) 2 4 (meaning1594 q) (meaning1619 q) (meaning1629 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1619 = false ∨ valuation q 1629 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-88, -90, -94, -95, -96, -97, -101]) + (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -96, -97, -101]) (l₂ := [-103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1628)) (countLit q [-88, -90, -94, -95, -96, -97, -101]) (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) (count1624 q) 3 2 (meaning1595 q) (meaning1617 q) (meaning1628 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1617 = false ∨ valuation q 1628 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-88, -90, -94, -95, -96, -97, -101]) + (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -96, -97, -101]) (l₂ := [-103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1629)) (countLit q [-88, -90, -94, -95, -96, -97, -101]) (countLit q [-103, -104, -106, -107, -111, -112, -113, -114]) (count1624 q) 3 3 (meaning1595 q) (meaning1618 q) (meaning1629 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1618 = false ∨ valuation q 1629 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1644 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1644)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 3 3 (meaning1568 q) (meaning1626 q) (meaning1644 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1626 = false ∨ valuation q 1644 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1645 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1645)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 3 4 (meaning1568 q) (meaning1627 q) (meaning1645 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1627 = false ∨ valuation q 1645 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E058.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112058
