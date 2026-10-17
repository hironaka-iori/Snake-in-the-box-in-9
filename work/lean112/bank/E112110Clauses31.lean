import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1551)) (countLit q [-61]) (countLit q [-63]) (count1551 q) 1 (meaningNeg61 q) (meaning1551 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1551 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1552 = true := by
  have hs : count1551 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1552)) (countLit q [-61]) (countLit q [-63]) (count1551 q) 1 1 (meaningNeg61 q) (meaningNeg63 q) (meaning1552 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 63 = true ∨ valuation q 1552 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-60]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1551)) (literal (valuationOf q) (1553)) (countLit q [-60]) (countLit q [-61, -63]) (count1553 q) 1 (meaning1551 q) (meaning1553 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1553 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-60]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1552)) (literal (valuationOf q) (1554)) (countLit q [-60]) (countLit q [-61, -63]) (count1553 q) 2 (meaning1552 q) (meaning1554 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1554 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-60]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -63])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1553)) (countLit q [-60]) (countLit q [-61, -63]) (count1553 q) 1 (meaningNeg60 q) (meaning1553 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1553 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-60]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -63])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1554)) (countLit q [-60]) (countLit q [-61, -63]) (count1553 q) 1 1 (meaningNeg60 q) (meaning1551 q) (meaning1554 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1551 = false ∨ valuation q 1554 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1552 = false ∨ valuationOf q 1555 = true := by
  have hs : count1553 q = (countLit q [-60]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -63])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1555)) (countLit q [-60]) (countLit q [-61, -63]) (count1553 q) 1 2 (meaningNeg60 q) (meaning1552 q) (meaning1555 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1552 = false ∨ valuation q 1555 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1556)) (countLit q [-64]) (countLit q [-66]) (count1556 q) 1 (meaningNeg66 q) (meaning1556 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1556 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1556)) (countLit q [-64]) (countLit q [-66]) (count1556 q) 1 (meaningNeg64 q) (meaning1556 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1556 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1557 = true := by
  have hs : count1556 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1557)) (countLit q [-64]) (countLit q [-66]) (count1556 q) 1 1 (meaningNeg64 q) (meaningNeg66 q) (meaning1557 q) hs
  change (! (valuationOf q 64)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 1557 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (1558)) (countLit q [-68]) (countLit q [-69]) (count1558 q) 1 (meaningNeg69 q) (meaning1558 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1558 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1558)) (countLit q [-68]) (countLit q [-69]) (count1558 q) 1 (meaningNeg68 q) (meaning1558 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1558 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 69 = true ∨ valuationOf q 1559 = true := by
  have hs : count1558 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_two (literal (valuationOf q) (-68)) (literal (valuationOf q) (-69)) (literal (valuationOf q) (1559)) (countLit q [-68]) (countLit q [-69]) (count1558 q) 1 1 (meaningNeg68 q) (meaningNeg69 q) (meaning1559 q) hs
  change (! (valuationOf q 68)) = false ∨ (! (valuationOf q 69)) = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 69 = true ∨ valuation q 1559 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-64, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-68, -69])
  have hm := merge_right (literal (valuationOf q) (1558)) (literal (valuationOf q) (1560)) (countLit q [-64, -66]) (countLit q [-68, -69]) (count1560 q) 1 (meaning1558 q) (meaning1560 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1560 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-64, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-68, -69])
  have hm := merge_right (literal (valuationOf q) (1559)) (literal (valuationOf q) (1561)) (countLit q [-64, -66]) (countLit q [-68, -69]) (count1560 q) 2 (meaning1559 q) (meaning1561 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1561 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-64, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-68, -69])
  have hm := merge_left (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-64, -66]) (countLit q [-68, -69]) (count1560 q) 1 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-64, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-68, -69])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1561)) (countLit q [-64, -66]) (countLit q [-68, -69]) (count1560 q) 1 1 (meaning1556 q) (meaning1558 q) (meaning1561 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1558 = false ∨ valuation q 1561 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true := by
  have hs : count1560 q = (countLit q [-64, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-68, -69])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1562)) (countLit q [-64, -66]) (countLit q [-68, -69]) (count1560 q) 1 2 (meaning1556 q) (meaning1559 q) (meaning1562 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1559 = false ∨ valuation q 1562 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-64, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-68, -69])
  have hm := merge_left (literal (valuationOf q) (1557)) (literal (valuationOf q) (1561)) (countLit q [-64, -66]) (countLit q [-68, -69]) (count1560 q) 2 (meaning1557 q) (meaning1561 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1561 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true := by
  have hs : count1560 q = (countLit q [-64, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-68, -69])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1562)) (countLit q [-64, -66]) (countLit q [-68, -69]) (count1560 q) 2 1 (meaning1557 q) (meaning1558 q) (meaning1562 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1558 = false ∨ valuation q 1562 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -63]) + (countLit q [-64, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63]) (l₂ := [-64, -66, -68, -69])
  have hm := merge_left (literal (valuationOf q) (1553)) (literal (valuationOf q) (1564)) (countLit q [-60, -61, -63]) (countLit q [-64, -66, -68, -69]) (count1564 q) 1 (meaning1553 q) (meaning1564 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1564 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -63]) + (countLit q [-64, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63]) (l₂ := [-64, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1565)) (countLit q [-60, -61, -63]) (countLit q [-64, -66, -68, -69]) (count1564 q) 1 1 (meaning1553 q) (meaning1560 q) (meaning1565 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1560 = false ∨ valuation q 1565 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -63]) + (countLit q [-64, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63]) (l₂ := [-64, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1566)) (countLit q [-60, -61, -63]) (countLit q [-64, -66, -68, -69]) (count1564 q) 1 2 (meaning1553 q) (meaning1561 q) (meaning1566 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1561 = false ∨ valuation q 1566 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1567 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -63]) + (countLit q [-64, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63]) (l₂ := [-64, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1567)) (countLit q [-60, -61, -63]) (countLit q [-64, -66, -68, -69]) (count1564 q) 1 3 (meaning1553 q) (meaning1562 q) (meaning1567 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1562 = false ∨ valuation q 1567 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -63]) + (countLit q [-64, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63]) (l₂ := [-64, -66, -68, -69])
  have hm := merge_left (literal (valuationOf q) (1554)) (literal (valuationOf q) (1565)) (countLit q [-60, -61, -63]) (countLit q [-64, -66, -68, -69]) (count1564 q) 2 (meaning1554 q) (meaning1565 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1565 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -63]) + (countLit q [-64, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63]) (l₂ := [-64, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1566)) (countLit q [-60, -61, -63]) (countLit q [-64, -66, -68, -69]) (count1564 q) 2 1 (meaning1554 q) (meaning1560 q) (meaning1566 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1560 = false ∨ valuation q 1566 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1567 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -63]) + (countLit q [-64, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63]) (l₂ := [-64, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1567)) (countLit q [-60, -61, -63]) (countLit q [-64, -66, -68, -69]) (count1564 q) 2 2 (meaning1554 q) (meaning1561 q) (meaning1567 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1561 = false ∨ valuation q 1567 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -63]) + (countLit q [-64, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63]) (l₂ := [-64, -66, -68, -69])
  have hm := merge_left (literal (valuationOf q) (1555)) (literal (valuationOf q) (1566)) (countLit q [-60, -61, -63]) (countLit q [-64, -66, -68, -69]) (count1564 q) 3 (meaning1555 q) (meaning1566 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1566 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1567 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -63]) + (countLit q [-64, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63]) (l₂ := [-64, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1567)) (countLit q [-60, -61, -63]) (countLit q [-64, -66, -68, -69]) (count1564 q) 3 1 (meaning1555 q) (meaning1560 q) (meaning1567 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1560 = false ∨ valuation q 1567 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1571)) (countLit q [-72]) (countLit q [-73]) (count1571 q) 1 (meaningNeg73 q) (meaning1571 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1571 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1571)) (countLit q [-72]) (countLit q [-73]) (count1571 q) 1 (meaningNeg72 q) (meaning1571 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1571 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1572)) (countLit q [-72]) (countLit q [-73]) (count1571 q) 1 1 (meaningNeg72 q) (meaningNeg73 q) (meaning1572 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 73 = true ∨ valuation q 1572 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E110.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112110
