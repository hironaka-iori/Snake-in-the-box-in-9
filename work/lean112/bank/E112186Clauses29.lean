import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-37, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -41]) (l₂ := [-42, -43])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1569)) (countLit q [-37, -41]) (countLit q [-42, -43]) (count1568 q) 1 1 (meaning1564 q) (meaning1566 q) (meaning1569 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1566 = false ∨ valuation q 1569 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-37, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -41]) (l₂ := [-42, -43])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1570)) (countLit q [-37, -41]) (countLit q [-42, -43]) (count1568 q) 1 2 (meaning1564 q) (meaning1567 q) (meaning1570 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1567 = false ∨ valuation q 1570 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-37, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -41]) (l₂ := [-42, -43])
  have hm := merge_left (literal (valuationOf q) (1565)) (literal (valuationOf q) (1569)) (countLit q [-37, -41]) (countLit q [-42, -43]) (count1568 q) 2 (meaning1565 q) (meaning1569 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1569 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-37, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -41]) (l₂ := [-42, -43])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1570)) (countLit q [-37, -41]) (countLit q [-42, -43]) (count1568 q) 2 1 (meaning1565 q) (meaning1566 q) (meaning1570 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1566 = false ∨ valuation q 1570 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1572 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_right (literal (valuationOf q) (1568)) (literal (valuationOf q) (1572)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 1 (meaning1568 q) (meaning1572 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1572 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1573 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_right (literal (valuationOf q) (1569)) (literal (valuationOf q) (1573)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 2 (meaning1569 q) (meaning1573 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1573 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1574 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_right (literal (valuationOf q) (1570)) (literal (valuationOf q) (1574)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 3 (meaning1570 q) (meaning1574 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1574 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1573 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1573)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 1 1 (meaning1560 q) (meaning1568 q) (meaning1573 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1568 = false ∨ valuation q 1573 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1574 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1574)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 1 2 (meaning1560 q) (meaning1569 q) (meaning1574 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1569 = false ∨ valuation q 1574 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1575 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1575)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 1 3 (meaning1560 q) (meaning1570 q) (meaning1575 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1570 = false ∨ valuation q 1575 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1574 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1574)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 2 1 (meaning1561 q) (meaning1568 q) (meaning1574 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1568 = false ∨ valuation q 1574 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1575 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1575)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 2 2 (meaning1561 q) (meaning1569 q) (meaning1575 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1569 = false ∨ valuation q 1575 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1576 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1576)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 2 3 (meaning1561 q) (meaning1570 q) (meaning1576 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1570 = false ∨ valuation q 1576 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1574 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_left (literal (valuationOf q) (1562)) (literal (valuationOf q) (1574)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 3 (meaning1562 q) (meaning1574 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1574 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1575 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1575)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 3 1 (meaning1562 q) (meaning1568 q) (meaning1575 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1568 = false ∨ valuation q 1575 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1576 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1576)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 3 2 (meaning1562 q) (meaning1569 q) (meaning1576 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1569 = false ∨ valuation q 1576 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1577 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1577)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 3 3 (meaning1562 q) (meaning1570 q) (meaning1577 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1570 = false ∨ valuation q 1577 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1576 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1576)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 4 1 (meaning1563 q) (meaning1568 q) (meaning1576 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1568 = false ∨ valuation q 1576 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1578 = true := by
  have hs : count1572 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-37, -41, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-37, -41, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1578)) (countLit q [-31, -33, -34, -36]) (countLit q [-37, -41, -42, -43]) (count1572 q) 4 3 (meaning1563 q) (meaning1570 q) (meaning1578 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1570 = false ∨ valuation q 1578 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-44]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1580)) (countLit q [-44]) (countLit q [-48]) (count1580 q) 1 (meaningNeg48 q) (meaning1580 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1580 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-44]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1580)) (countLit q [-44]) (countLit q [-48]) (count1580 q) 1 (meaningNeg44 q) (meaning1580 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1580 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 48 = true ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-44]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (1581)) (countLit q [-44]) (countLit q [-48]) (count1580 q) 1 1 (meaningNeg44 q) (meaningNeg48 q) (meaning1581 q) hs
  change (! (valuationOf q 44)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 48 = true ∨ valuation q 1581 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1582)) (countLit q [-50]) (countLit q [-51]) (count1582 q) 1 (meaningNeg51 q) (meaning1582 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1582 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1582)) (countLit q [-50]) (countLit q [-51]) (count1582 q) 1 (meaningNeg50 q) (meaning1582 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1582 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1583)) (countLit q [-50]) (countLit q [-51]) (count1582 q) 1 1 (meaningNeg50 q) (meaningNeg51 q) (meaning1583 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 1583 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1584 = true := by
  have hs : count1584 q = (countLit q [-44, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -48]) (l₂ := [-50, -51])
  have hm := merge_right (literal (valuationOf q) (1582)) (literal (valuationOf q) (1584)) (countLit q [-44, -48]) (countLit q [-50, -51]) (count1584 q) 1 (meaning1582 q) (meaning1584 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1584 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-44, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -48]) (l₂ := [-50, -51])
  have hm := merge_right (literal (valuationOf q) (1583)) (literal (valuationOf q) (1585)) (countLit q [-44, -48]) (countLit q [-50, -51]) (count1584 q) 2 (meaning1583 q) (meaning1585 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1585 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1584 = true := by
  have hs : count1584 q = (countLit q [-44, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -48]) (l₂ := [-50, -51])
  have hm := merge_left (literal (valuationOf q) (1580)) (literal (valuationOf q) (1584)) (countLit q [-44, -48]) (countLit q [-50, -51]) (count1584 q) 1 (meaning1580 q) (meaning1584 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1584 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-44, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -48]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1585)) (countLit q [-44, -48]) (countLit q [-50, -51]) (count1584 q) 1 1 (meaning1580 q) (meaning1582 q) (meaning1585 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1582 = false ∨ valuation q 1585 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1586 = true := by
  have hs : count1584 q = (countLit q [-44, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -48]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1586)) (countLit q [-44, -48]) (countLit q [-50, -51]) (count1584 q) 1 2 (meaning1580 q) (meaning1583 q) (meaning1586 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1583 = false ∨ valuation q 1586 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-44, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -48]) (l₂ := [-50, -51])
  have hm := merge_left (literal (valuationOf q) (1581)) (literal (valuationOf q) (1585)) (countLit q [-44, -48]) (countLit q [-50, -51]) (count1584 q) 2 (meaning1581 q) (meaning1585 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1585 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1586 = true := by
  have hs : count1584 q = (countLit q [-44, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -48]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1586)) (countLit q [-44, -48]) (countLit q [-50, -51]) (count1584 q) 2 1 (meaning1581 q) (meaning1582 q) (meaning1586 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1582 = false ∨ valuation q 1586 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E186.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112186
