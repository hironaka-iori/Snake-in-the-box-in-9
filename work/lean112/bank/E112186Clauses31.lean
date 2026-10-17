import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1607 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1607)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 2 2 (meaning1573 q) (meaning1597 q) (meaning1607 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1597 = false ∨ valuation q 1607 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1608 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1608)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 2 3 (meaning1573 q) (meaning1598 q) (meaning1608 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1598 = false ∨ valuation q 1608 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1609 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1609)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 2 4 (meaning1573 q) (meaning1599 q) (meaning1609 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1599 = false ∨ valuation q 1609 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1610 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1610)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 2 5 (meaning1573 q) (meaning1600 q) (meaning1610 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1600 = false ∨ valuation q 1610 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1607 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1607)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 3 1 (meaning1574 q) (meaning1596 q) (meaning1607 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1596 = false ∨ valuation q 1607 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1608 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1608)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 3 2 (meaning1574 q) (meaning1597 q) (meaning1608 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1597 = false ∨ valuation q 1608 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1609 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1609)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 3 3 (meaning1574 q) (meaning1598 q) (meaning1609 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1598 = false ∨ valuation q 1609 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1610 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1610)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 3 4 (meaning1574 q) (meaning1599 q) (meaning1610 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1599 = false ∨ valuation q 1610 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1611 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1611)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 3 5 (meaning1574 q) (meaning1600 q) (meaning1611 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1600 = false ∨ valuation q 1611 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1608 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1608)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 4 1 (meaning1575 q) (meaning1596 q) (meaning1608 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1596 = false ∨ valuation q 1608 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1609 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1609)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 4 2 (meaning1575 q) (meaning1597 q) (meaning1609 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1597 = false ∨ valuation q 1609 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1610 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1610)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 4 3 (meaning1575 q) (meaning1598 q) (meaning1610 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1598 = false ∨ valuation q 1610 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1611 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1611)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 4 4 (meaning1575 q) (meaning1599 q) (meaning1611 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1599 = false ∨ valuation q 1611 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1612 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1612)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 4 5 (meaning1575 q) (meaning1600 q) (meaning1612 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1600 = false ∨ valuation q 1612 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1609 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1609)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 5 1 (meaning1576 q) (meaning1596 q) (meaning1609 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1596 = false ∨ valuation q 1609 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1610 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1610)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 5 2 (meaning1576 q) (meaning1597 q) (meaning1610 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1597 = false ∨ valuation q 1610 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1611 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1611)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 5 3 (meaning1576 q) (meaning1598 q) (meaning1611 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1598 = false ∨ valuation q 1611 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1612 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1612)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 5 4 (meaning1576 q) (meaning1599 q) (meaning1612 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1599 = false ∨ valuation q 1612 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1613 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1613)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 5 5 (meaning1576 q) (meaning1600 q) (meaning1613 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1600 = false ∨ valuation q 1613 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1610 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1610)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 6 1 (meaning1577 q) (meaning1596 q) (meaning1610 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1596 = false ∨ valuation q 1610 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1611 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1611)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 6 2 (meaning1577 q) (meaning1597 q) (meaning1611 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1597 = false ∨ valuation q 1611 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1612 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1612)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 7 2 (meaning1578 q) (meaning1597 q) (meaning1612 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1597 = false ∨ valuation q 1612 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1626 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1626)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 3 4 (meaning1543 q) (meaning1607 q) (meaning1626 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1607 = false ∨ valuation q 1626 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1627 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1627)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 3 5 (meaning1543 q) (meaning1608 q) (meaning1627 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1608 = false ∨ valuation q 1627 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1628 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1628)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 3 6 (meaning1543 q) (meaning1609 q) (meaning1628 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1609 = false ∨ valuation q 1628 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1629 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1629)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 3 7 (meaning1543 q) (meaning1610 q) (meaning1629 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1610 = false ∨ valuation q 1629 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1630 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1630)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 3 8 (meaning1543 q) (meaning1611 q) (meaning1630 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1611 = false ∨ valuation q 1630 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1631 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1631)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 3 9 (meaning1543 q) (meaning1612 q) (meaning1631 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1612 = false ∨ valuation q 1631 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1626 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1626)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 4 3 (meaning1544 q) (meaning1606 q) (meaning1626 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1606 = false ∨ valuation q 1626 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1627 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1627)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 4 4 (meaning1544 q) (meaning1607 q) (meaning1627 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1607 = false ∨ valuation q 1627 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1628 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1628)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 4 5 (meaning1544 q) (meaning1608 q) (meaning1628 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1608 = false ∨ valuation q 1628 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1629 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1629)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 4 6 (meaning1544 q) (meaning1609 q) (meaning1629 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1609 = false ∨ valuation q 1629 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E186.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112186
