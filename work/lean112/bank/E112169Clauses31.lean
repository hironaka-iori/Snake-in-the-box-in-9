import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1567 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_right (literal (valuationOf q) (1560)) (literal (valuationOf q) (1567)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 2 (meaning1560 q) (meaning1567 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1567 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1568 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_right (literal (valuationOf q) (1561)) (literal (valuationOf q) (1568)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 3 (meaning1561 q) (meaning1568 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1568 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1566 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_left (literal (valuationOf q) (1539)) (literal (valuationOf q) (1566)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 1 (meaning1539 q) (meaning1566 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1566 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1567 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1567)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 1 1 (meaning1539 q) (meaning1559 q) (meaning1567 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1559 = false ∨ valuation q 1567 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1568 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1568)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 1 2 (meaning1539 q) (meaning1560 q) (meaning1568 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1560 = false ∨ valuation q 1568 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1567 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_left (literal (valuationOf q) (1540)) (literal (valuationOf q) (1567)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 2 (meaning1540 q) (meaning1567 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1567 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1568 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1568)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 2 1 (meaning1540 q) (meaning1559 q) (meaning1568 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1559 = false ∨ valuation q 1568 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1569)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 2 2 (meaning1540 q) (meaning1560 q) (meaning1569 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1560 = false ∨ valuation q 1569 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1570)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 2 3 (meaning1540 q) (meaning1561 q) (meaning1570 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1561 = false ∨ valuation q 1570 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1568 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_left (literal (valuationOf q) (1541)) (literal (valuationOf q) (1568)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 3 (meaning1541 q) (meaning1568 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1568 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1569)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 3 1 (meaning1541 q) (meaning1559 q) (meaning1569 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1559 = false ∨ valuation q 1569 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1570)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 3 2 (meaning1541 q) (meaning1560 q) (meaning1570 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1560 = false ∨ valuation q 1570 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_left (literal (valuationOf q) (1542)) (literal (valuationOf q) (1569)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 4 (meaning1542 q) (meaning1569 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1569 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1570)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 4 1 (meaning1542 q) (meaning1559 q) (meaning1570 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1559 = false ∨ valuation q 1570 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-88]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (1580)) (countLit q [-88]) (countLit q [-91]) (count1580 q) 1 (meaningNeg91 q) (meaning1580 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1580 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-88]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1580)) (countLit q [-88]) (countLit q [-91]) (count1580 q) 1 (meaningNeg88 q) (meaning1580 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1580 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 91 = true ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-88]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (-91)) (literal (valuationOf q) (1581)) (countLit q [-88]) (countLit q [-91]) (count1580 q) 1 1 (meaningNeg88 q) (meaningNeg91 q) (meaning1581 q) hs
  change (! (valuationOf q 88)) = false ∨ (! (valuationOf q 91)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 1581 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-86]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -91])
  have hm := merge_right (literal (valuationOf q) (1580)) (literal (valuationOf q) (1582)) (countLit q [-86]) (countLit q [-88, -91]) (count1582 q) 1 (meaning1580 q) (meaning1582 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1582 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-86]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -91])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1583)) (countLit q [-86]) (countLit q [-88, -91]) (count1582 q) 2 (meaning1581 q) (meaning1583 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1583 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-86]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -91])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1582)) (countLit q [-86]) (countLit q [-88, -91]) (count1582 q) 1 (meaningNeg86 q) (meaning1582 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1582 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1580 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-86]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -91])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1583)) (countLit q [-86]) (countLit q [-88, -91]) (count1582 q) 1 1 (meaningNeg86 q) (meaning1580 q) (meaning1583 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1580 = false ∨ valuation q 1583 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-86]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -91])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1584)) (countLit q [-86]) (countLit q [-88, -91]) (count1582 q) 1 2 (meaningNeg86 q) (meaning1581 q) (meaning1584 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1581 = false ∨ valuation q 1584 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1585)) (countLit q [-93]) (countLit q [-94]) (count1585 q) 1 (meaningNeg94 q) (meaning1585 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1585 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1585)) (countLit q [-93]) (countLit q [-94]) (count1585 q) 1 (meaningNeg93 q) (meaning1585 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1585 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 94 = true ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (1586)) (countLit q [-93]) (countLit q [-94]) (count1585 q) 1 1 (meaningNeg93 q) (meaningNeg94 q) (meaning1586 q) hs
  change (! (valuationOf q 93)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 94 = true ∨ valuation q 1586 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-97]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1587)) (countLit q [-97]) (countLit q [-100]) (count1587 q) 1 (meaningNeg100 q) (meaning1587 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1587 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-97]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1587)) (countLit q [-97]) (countLit q [-100]) (count1587 q) 1 (meaningNeg97 q) (meaning1587 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1587 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-97]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1588)) (countLit q [-97]) (countLit q [-100]) (count1587 q) 1 1 (meaningNeg97 q) (meaningNeg100 q) (meaning1588 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 100 = true ∨ valuation q 1588 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-93, -94]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-97, -100])
  have hm := merge_right (literal (valuationOf q) (1587)) (literal (valuationOf q) (1589)) (countLit q [-93, -94]) (countLit q [-97, -100]) (count1589 q) 1 (meaning1587 q) (meaning1589 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1589 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-93, -94]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-97, -100])
  have hm := merge_right (literal (valuationOf q) (1588)) (literal (valuationOf q) (1590)) (countLit q [-93, -94]) (countLit q [-97, -100]) (count1589 q) 2 (meaning1588 q) (meaning1590 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1590 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-93, -94]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-97, -100])
  have hm := merge_left (literal (valuationOf q) (1585)) (literal (valuationOf q) (1589)) (countLit q [-93, -94]) (countLit q [-97, -100]) (count1589 q) 1 (meaning1585 q) (meaning1589 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1589 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-93, -94]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-97, -100])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1590)) (countLit q [-93, -94]) (countLit q [-97, -100]) (count1589 q) 1 1 (meaning1585 q) (meaning1587 q) (meaning1590 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1587 = false ∨ valuation q 1590 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E169.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112169
