import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1621 = true := by
  have hs : count1619 q = (countLit q [-97, -99]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-101, -102])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1621)) (countLit q [-97, -99]) (countLit q [-101, -102]) (count1619 q) 2 1 (meaning1616 q) (meaning1617 q) (meaning1621 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1617 = false ∨ valuation q 1621 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1622 = true := by
  have hs : count1619 q = (countLit q [-97, -99]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-101, -102])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1622)) (countLit q [-97, -99]) (countLit q [-101, -102]) (count1619 q) 2 2 (meaning1616 q) (meaning1618 q) (meaning1622 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1618 = false ∨ valuation q 1622 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-90, -93, -94]) + (countLit q [-97, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-97, -99, -101, -102])
  have hm := merge_right (literal (valuationOf q) (1619)) (literal (valuationOf q) (1623)) (countLit q [-90, -93, -94]) (countLit q [-97, -99, -101, -102]) (count1623 q) 1 (meaning1619 q) (meaning1623 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1623 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-90, -93, -94]) + (countLit q [-97, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-97, -99, -101, -102])
  have hm := merge_right (literal (valuationOf q) (1620)) (literal (valuationOf q) (1624)) (countLit q [-90, -93, -94]) (countLit q [-97, -99, -101, -102]) (count1623 q) 2 (meaning1620 q) (meaning1624 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1624 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-90, -93, -94]) + (countLit q [-97, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-97, -99, -101, -102])
  have hm := merge_right (literal (valuationOf q) (1621)) (literal (valuationOf q) (1625)) (countLit q [-90, -93, -94]) (countLit q [-97, -99, -101, -102]) (count1623 q) 3 (meaning1621 q) (meaning1625 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1625 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-90, -93, -94]) + (countLit q [-97, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-97, -99, -101, -102])
  have hm := merge_right (literal (valuationOf q) (1622)) (literal (valuationOf q) (1626)) (countLit q [-90, -93, -94]) (countLit q [-97, -99, -101, -102]) (count1623 q) 4 (meaning1622 q) (meaning1626 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1626 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-90, -93, -94]) + (countLit q [-97, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-97, -99, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1612)) (literal (valuationOf q) (1623)) (countLit q [-90, -93, -94]) (countLit q [-97, -99, -101, -102]) (count1623 q) 1 (meaning1612 q) (meaning1623 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1623 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-90, -93, -94]) + (countLit q [-97, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-97, -99, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1624)) (countLit q [-90, -93, -94]) (countLit q [-97, -99, -101, -102]) (count1623 q) 1 1 (meaning1612 q) (meaning1619 q) (meaning1624 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1619 = false ∨ valuation q 1624 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-90, -93, -94]) + (countLit q [-97, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-97, -99, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1625)) (countLit q [-90, -93, -94]) (countLit q [-97, -99, -101, -102]) (count1623 q) 1 2 (meaning1612 q) (meaning1620 q) (meaning1625 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1620 = false ∨ valuation q 1625 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-90, -93, -94]) + (countLit q [-97, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-97, -99, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1626)) (countLit q [-90, -93, -94]) (countLit q [-97, -99, -101, -102]) (count1623 q) 1 3 (meaning1612 q) (meaning1621 q) (meaning1626 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1621 = false ∨ valuation q 1626 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1627 = true := by
  have hs : count1623 q = (countLit q [-90, -93, -94]) + (countLit q [-97, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-97, -99, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1627)) (countLit q [-90, -93, -94]) (countLit q [-97, -99, -101, -102]) (count1623 q) 1 4 (meaning1612 q) (meaning1622 q) (meaning1627 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1622 = false ∨ valuation q 1627 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-90, -93, -94]) + (countLit q [-97, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-97, -99, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1613)) (literal (valuationOf q) (1624)) (countLit q [-90, -93, -94]) (countLit q [-97, -99, -101, -102]) (count1623 q) 2 (meaning1613 q) (meaning1624 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1624 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-90, -93, -94]) + (countLit q [-97, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-97, -99, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1625)) (countLit q [-90, -93, -94]) (countLit q [-97, -99, -101, -102]) (count1623 q) 2 1 (meaning1613 q) (meaning1619 q) (meaning1625 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1619 = false ∨ valuation q 1625 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-90, -93, -94]) + (countLit q [-97, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-97, -99, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1626)) (countLit q [-90, -93, -94]) (countLit q [-97, -99, -101, -102]) (count1623 q) 2 2 (meaning1613 q) (meaning1620 q) (meaning1626 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1620 = false ∨ valuation q 1626 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1627 = true := by
  have hs : count1623 q = (countLit q [-90, -93, -94]) + (countLit q [-97, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-97, -99, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1627)) (countLit q [-90, -93, -94]) (countLit q [-97, -99, -101, -102]) (count1623 q) 2 3 (meaning1613 q) (meaning1621 q) (meaning1627 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1621 = false ∨ valuation q 1627 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-105]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1630)) (countLit q [-105]) (countLit q [-107]) (count1630 q) 1 (meaningNeg107 q) (meaning1630 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1630 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-105]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-105)) (literal (valuationOf q) (1630)) (countLit q [-105]) (countLit q [-107]) (count1630 q) 1 (meaningNeg105 q) (meaning1630 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1630 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1631 = true := by
  have hs : count1630 q = (countLit q [-105]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-105)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1631)) (countLit q [-105]) (countLit q [-107]) (count1630 q) 1 1 (meaningNeg105 q) (meaningNeg107 q) (meaning1631 q) hs
  change (! (valuationOf q 105)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 107 = true ∨ valuation q 1631 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-108]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-109])
  have hm := merge_right (literal (valuationOf q) (-109)) (literal (valuationOf q) (1632)) (countLit q [-108]) (countLit q [-109]) (count1632 q) 1 (meaningNeg109 q) (meaning1632 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1632 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-108]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-109])
  have hm := merge_left (literal (valuationOf q) (-108)) (literal (valuationOf q) (1632)) (countLit q [-108]) (countLit q [-109]) (count1632 q) 1 (meaningNeg108 q) (meaning1632 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1632 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 109 = true ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-108]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-109])
  have hm := merge_two (literal (valuationOf q) (-108)) (literal (valuationOf q) (-109)) (literal (valuationOf q) (1633)) (countLit q [-108]) (countLit q [-109]) (count1632 q) 1 1 (meaningNeg108 q) (meaningNeg109 q) (meaning1633 q) hs
  change (! (valuationOf q 108)) = false ∨ (! (valuationOf q 109)) = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 109 = true ∨ valuation q 1633 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-105, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -107]) (l₂ := [-108, -109])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1634)) (countLit q [-105, -107]) (countLit q [-108, -109]) (count1634 q) 1 (meaning1632 q) (meaning1634 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1634 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-105, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -107]) (l₂ := [-108, -109])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1635)) (countLit q [-105, -107]) (countLit q [-108, -109]) (count1634 q) 2 (meaning1633 q) (meaning1635 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1635 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-105, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -107]) (l₂ := [-108, -109])
  have hm := merge_left (literal (valuationOf q) (1630)) (literal (valuationOf q) (1634)) (countLit q [-105, -107]) (countLit q [-108, -109]) (count1634 q) 1 (meaning1630 q) (meaning1634 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1634 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-105, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -107]) (l₂ := [-108, -109])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1635)) (countLit q [-105, -107]) (countLit q [-108, -109]) (count1634 q) 1 1 (meaning1630 q) (meaning1632 q) (meaning1635 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1632 = false ∨ valuation q 1635 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-105, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -107]) (l₂ := [-108, -109])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1636)) (countLit q [-105, -107]) (countLit q [-108, -109]) (count1634 q) 1 2 (meaning1630 q) (meaning1633 q) (meaning1636 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1633 = false ∨ valuation q 1636 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-105, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -107]) (l₂ := [-108, -109])
  have hm := merge_left (literal (valuationOf q) (1631)) (literal (valuationOf q) (1635)) (countLit q [-105, -107]) (countLit q [-108, -109]) (count1634 q) 2 (meaning1631 q) (meaning1635 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1635 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-105, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -107]) (l₂ := [-108, -109])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1636)) (countLit q [-105, -107]) (countLit q [-108, -109]) (count1634 q) 2 1 (meaning1631 q) (meaning1632 q) (meaning1636 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1632 = false ∨ valuation q 1636 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1637 = true := by
  have hs : count1634 q = (countLit q [-105, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -107]) (l₂ := [-108, -109])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1637)) (countLit q [-105, -107]) (countLit q [-108, -109]) (count1634 q) 2 2 (meaning1631 q) (meaning1633 q) (meaning1637 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1633 = false ∨ valuation q 1637 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1638 = true := by
  have hs : count1638 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_right (literal (valuationOf q) (-112)) (literal (valuationOf q) (1638)) (countLit q [-111]) (countLit q [-112]) (count1638 q) 1 (meaningNeg112 q) (meaning1638 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1638 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1638 = true := by
  have hs : count1638 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1638)) (countLit q [-111]) (countLit q [-112]) (count1638 q) 1 (meaningNeg111 q) (meaning1638 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1638 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 112 = true ∨ valuationOf q 1639 = true := by
  have hs : count1638 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-112)) (literal (valuationOf q) (1639)) (countLit q [-111]) (countLit q [-112]) (count1638 q) 1 1 (meaningNeg111 q) (meaningNeg112 q) (meaning1639 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 112)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 1639 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E104.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112104
