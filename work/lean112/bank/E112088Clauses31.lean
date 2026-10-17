import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1563 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1563)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 1 2 (meaning1530 q) (meaning1554 q) (meaning1563 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1554 = false ∨ valuation q 1563 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1562 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_left (literal (valuationOf q) (1531)) (literal (valuationOf q) (1562)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 2 (meaning1531 q) (meaning1562 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1562 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1563 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1563)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 2 1 (meaning1531 q) (meaning1553 q) (meaning1563 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1553 = false ∨ valuation q 1563 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1564 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1564)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 2 2 (meaning1531 q) (meaning1554 q) (meaning1564 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1554 = false ∨ valuation q 1564 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1563 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_left (literal (valuationOf q) (1532)) (literal (valuationOf q) (1563)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 3 (meaning1532 q) (meaning1563 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1563 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1564 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1564)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 3 1 (meaning1532 q) (meaning1553 q) (meaning1564 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1553 = false ∨ valuation q 1564 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1565 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1565)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 3 2 (meaning1532 q) (meaning1554 q) (meaning1565 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1554 = false ∨ valuation q 1565 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1566 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1566)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 3 3 (meaning1532 q) (meaning1555 q) (meaning1566 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1555 = false ∨ valuation q 1566 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1567 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1567)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 3 4 (meaning1532 q) (meaning1556 q) (meaning1567 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1556 = false ∨ valuation q 1567 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1568 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1568)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 3 5 (meaning1532 q) (meaning1557 q) (meaning1568 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1557 = false ∨ valuation q 1568 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1565 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1565)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 4 1 (meaning1533 q) (meaning1553 q) (meaning1565 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1553 = false ∨ valuation q 1565 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1566 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1566)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 4 2 (meaning1533 q) (meaning1554 q) (meaning1566 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1554 = false ∨ valuation q 1566 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1567 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1567)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 4 3 (meaning1533 q) (meaning1555 q) (meaning1567 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1555 = false ∨ valuation q 1567 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1568 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1568)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 4 4 (meaning1533 q) (meaning1556 q) (meaning1568 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1556 = false ∨ valuation q 1568 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1566 = true := by
  have hs : count1561 q = (countLit q [-59, -61, -63, -64, -66, -69, -71]) + (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71]) (l₂ := [-73, -75, -77, -78, -80, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1566)) (countLit q [-59, -61, -63, -64, -66, -69, -71]) (countLit q [-73, -75, -77, -78, -80, -82, -85, -87]) (count1561 q) 5 1 (meaning1534 q) (meaning1553 q) (meaning1566 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1553 = false ∨ valuation q 1566 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-90]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92])
  have hm := merge_right (literal (valuationOf q) (-92)) (literal (valuationOf q) (1576)) (countLit q [-90]) (countLit q [-92]) (count1576 q) 1 (meaningNeg92 q) (meaning1576 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1576 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-90]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1576)) (countLit q [-90]) (countLit q [-92]) (count1576 q) 1 (meaningNeg90 q) (meaning1576 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1576 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 92 = true ∨ valuationOf q 1577 = true := by
  have hs : count1576 q = (countLit q [-90]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (-92)) (literal (valuationOf q) (1577)) (countLit q [-90]) (countLit q [-92]) (count1576 q) 1 1 (meaningNeg90 q) (meaningNeg92 q) (meaning1577 q) hs
  change (! (valuationOf q 90)) = false ∨ (! (valuationOf q 92)) = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 92 = true ∨ valuation q 1577 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-88]) + (countLit q [-90, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -92])
  have hm := merge_right (literal (valuationOf q) (1576)) (literal (valuationOf q) (1578)) (countLit q [-88]) (countLit q [-90, -92]) (count1578 q) 1 (meaning1576 q) (meaning1578 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1578 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1579 = true := by
  have hs : count1578 q = (countLit q [-88]) + (countLit q [-90, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -92])
  have hm := merge_right (literal (valuationOf q) (1577)) (literal (valuationOf q) (1579)) (countLit q [-88]) (countLit q [-90, -92]) (count1578 q) 2 (meaning1577 q) (meaning1579 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1579 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-88]) + (countLit q [-90, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -92])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1578)) (countLit q [-88]) (countLit q [-90, -92]) (count1578 q) 1 (meaningNeg88 q) (meaning1578 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1578 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1576 = false ∨ valuationOf q 1579 = true := by
  have hs : count1578 q = (countLit q [-88]) + (countLit q [-90, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -92])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1579)) (countLit q [-88]) (countLit q [-90, -92]) (count1578 q) 1 1 (meaningNeg88 q) (meaning1576 q) (meaning1579 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1576 = false ∨ valuation q 1579 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1577 = false ∨ valuationOf q 1580 = true := by
  have hs : count1578 q = (countLit q [-88]) + (countLit q [-90, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -92])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1580)) (countLit q [-88]) (countLit q [-90, -92]) (count1578 q) 1 2 (meaningNeg88 q) (meaning1577 q) (meaning1580 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1577 = false ∨ valuation q 1580 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1581 = true := by
  have hs : count1581 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_right (literal (valuationOf q) (-95)) (literal (valuationOf q) (1581)) (countLit q [-94]) (countLit q [-95]) (count1581 q) 1 (meaningNeg95 q) (meaning1581 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1581 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1581 = true := by
  have hs : count1581 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1581)) (countLit q [-94]) (countLit q [-95]) (count1581 q) 1 (meaningNeg94 q) (meaning1581 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1581 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 95 = true ∨ valuationOf q 1582 = true := by
  have hs : count1581 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-95)) (literal (valuationOf q) (1582)) (countLit q [-94]) (countLit q [-95]) (count1581 q) 1 1 (meaningNeg94 q) (meaningNeg95 q) (meaning1582 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 95)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 95 = true ∨ valuation q 1582 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-97]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1583)) (countLit q [-97]) (countLit q [-100]) (count1583 q) 1 (meaningNeg100 q) (meaning1583 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1583 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-97]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1583)) (countLit q [-97]) (countLit q [-100]) (count1583 q) 1 (meaningNeg97 q) (meaning1583 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1583 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-97]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1584)) (countLit q [-97]) (countLit q [-100]) (count1583 q) 1 1 (meaningNeg97 q) (meaningNeg100 q) (meaning1584 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 100 = true ∨ valuation q 1584 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-94, -95]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-97, -100])
  have hm := merge_right (literal (valuationOf q) (1583)) (literal (valuationOf q) (1585)) (countLit q [-94, -95]) (countLit q [-97, -100]) (count1585 q) 1 (meaning1583 q) (meaning1585 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1585 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-94, -95]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-97, -100])
  have hm := merge_right (literal (valuationOf q) (1584)) (literal (valuationOf q) (1586)) (countLit q [-94, -95]) (countLit q [-97, -100]) (count1585 q) 2 (meaning1584 q) (meaning1586 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1586 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-94, -95]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-97, -100])
  have hm := merge_left (literal (valuationOf q) (1581)) (literal (valuationOf q) (1585)) (countLit q [-94, -95]) (countLit q [-97, -100]) (count1585 q) 1 (meaning1581 q) (meaning1585 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1585 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E088.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112088
