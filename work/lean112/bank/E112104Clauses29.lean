import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 80 = true ∨ valuationOf q 1574 = true := by
  have hs : count1573 q = (countLit q [-77]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (1574)) (countLit q [-77]) (countLit q [-80]) (count1573 q) 1 1 (meaningNeg77 q) (meaningNeg80 q) (meaning1574 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 80 = true ∨ valuation q 1574 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-73, -76]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-73, -76]) (l₂ := [-77, -80])
  have hm := merge_right (literal (valuationOf q) (1573)) (literal (valuationOf q) (1575)) (countLit q [-73, -76]) (countLit q [-77, -80]) (count1575 q) 1 (meaning1573 q) (meaning1575 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1575 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-73, -76]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-73, -76]) (l₂ := [-77, -80])
  have hm := merge_right (literal (valuationOf q) (1574)) (literal (valuationOf q) (1576)) (countLit q [-73, -76]) (countLit q [-77, -80]) (count1575 q) 2 (meaning1574 q) (meaning1576 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1576 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-73, -76]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-73, -76]) (l₂ := [-77, -80])
  have hm := merge_left (literal (valuationOf q) (1571)) (literal (valuationOf q) (1575)) (countLit q [-73, -76]) (countLit q [-77, -80]) (count1575 q) 1 (meaning1571 q) (meaning1575 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1575 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-73, -76]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-73, -76]) (l₂ := [-77, -80])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1576)) (countLit q [-73, -76]) (countLit q [-77, -80]) (count1575 q) 1 1 (meaning1571 q) (meaning1573 q) (meaning1576 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1573 = false ∨ valuation q 1576 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-73, -76]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-73, -76]) (l₂ := [-77, -80])
  have hm := merge_left (literal (valuationOf q) (1572)) (literal (valuationOf q) (1576)) (countLit q [-73, -76]) (countLit q [-77, -80]) (count1575 q) 2 (meaning1572 q) (meaning1576 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1576 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1579)) (countLit q [-82]) (countLit q [-84]) (count1579 q) 1 (meaningNeg84 q) (meaning1579 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1579 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1579)) (countLit q [-82]) (countLit q [-84]) (count1579 q) 1 (meaningNeg82 q) (meaning1579 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1579 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 84 = true ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (1580)) (countLit q [-82]) (countLit q [-84]) (count1579 q) 1 1 (meaningNeg82 q) (meaningNeg84 q) (meaning1580 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 1580 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1581 = true := by
  have hs : count1581 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1581)) (countLit q [-86]) (countLit q [-89]) (count1581 q) 1 (meaningNeg89 q) (meaning1581 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1581 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1581 = true := by
  have hs : count1581 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1581)) (countLit q [-86]) (countLit q [-89]) (count1581 q) 1 (meaningNeg86 q) (meaning1581 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1581 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 89 = true ∨ valuationOf q 1582 = true := by
  have hs : count1581 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-89)) (literal (valuationOf q) (1582)) (countLit q [-86]) (countLit q [-89]) (count1581 q) 1 1 (meaningNeg86 q) (meaningNeg89 q) (meaning1582 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 89)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 89 = true ∨ valuation q 1582 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-82, -84]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -89])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1583)) (countLit q [-82, -84]) (countLit q [-86, -89]) (count1583 q) 1 (meaning1581 q) (meaning1583 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1583 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-82, -84]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -89])
  have hm := merge_right (literal (valuationOf q) (1582)) (literal (valuationOf q) (1584)) (countLit q [-82, -84]) (countLit q [-86, -89]) (count1583 q) 2 (meaning1582 q) (meaning1584 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1584 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-82, -84]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -89])
  have hm := merge_left (literal (valuationOf q) (1579)) (literal (valuationOf q) (1583)) (countLit q [-82, -84]) (countLit q [-86, -89]) (count1583 q) 1 (meaning1579 q) (meaning1583 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1583 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-82, -84]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1584)) (countLit q [-82, -84]) (countLit q [-86, -89]) (count1583 q) 1 1 (meaning1579 q) (meaning1581 q) (meaning1584 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1581 = false ∨ valuation q 1584 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1585 = true := by
  have hs : count1583 q = (countLit q [-82, -84]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1585)) (countLit q [-82, -84]) (countLit q [-86, -89]) (count1583 q) 1 2 (meaning1579 q) (meaning1582 q) (meaning1585 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1582 = false ∨ valuation q 1585 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-82, -84]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -89])
  have hm := merge_left (literal (valuationOf q) (1580)) (literal (valuationOf q) (1584)) (countLit q [-82, -84]) (countLit q [-86, -89]) (count1583 q) 2 (meaning1580 q) (meaning1584 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1584 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1585 = true := by
  have hs : count1583 q = (countLit q [-82, -84]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1585)) (countLit q [-82, -84]) (countLit q [-86, -89]) (count1583 q) 2 1 (meaning1580 q) (meaning1581 q) (meaning1585 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1581 = false ∨ valuation q 1585 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-73, -76, -77, -80]) + (countLit q [-82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -76, -77, -80]) (l₂ := [-82, -84, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1583)) (literal (valuationOf q) (1587)) (countLit q [-73, -76, -77, -80]) (countLit q [-82, -84, -86, -89]) (count1587 q) 1 (meaning1583 q) (meaning1587 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1587 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-73, -76, -77, -80]) + (countLit q [-82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -76, -77, -80]) (l₂ := [-82, -84, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1584)) (literal (valuationOf q) (1588)) (countLit q [-73, -76, -77, -80]) (countLit q [-82, -84, -86, -89]) (count1587 q) 2 (meaning1584 q) (meaning1588 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1588 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-73, -76, -77, -80]) + (countLit q [-82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -76, -77, -80]) (l₂ := [-82, -84, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1585)) (literal (valuationOf q) (1589)) (countLit q [-73, -76, -77, -80]) (countLit q [-82, -84, -86, -89]) (count1587 q) 3 (meaning1585 q) (meaning1589 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1589 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-73, -76, -77, -80]) + (countLit q [-82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -76, -77, -80]) (l₂ := [-82, -84, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1575)) (literal (valuationOf q) (1587)) (countLit q [-73, -76, -77, -80]) (countLit q [-82, -84, -86, -89]) (count1587 q) 1 (meaning1575 q) (meaning1587 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1587 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-73, -76, -77, -80]) + (countLit q [-82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -76, -77, -80]) (l₂ := [-82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1588)) (countLit q [-73, -76, -77, -80]) (countLit q [-82, -84, -86, -89]) (count1587 q) 1 1 (meaning1575 q) (meaning1583 q) (meaning1588 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1583 = false ∨ valuation q 1588 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-73, -76, -77, -80]) + (countLit q [-82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -76, -77, -80]) (l₂ := [-82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1589)) (countLit q [-73, -76, -77, -80]) (countLit q [-82, -84, -86, -89]) (count1587 q) 1 2 (meaning1575 q) (meaning1584 q) (meaning1589 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1584 = false ∨ valuation q 1589 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1590 = true := by
  have hs : count1587 q = (countLit q [-73, -76, -77, -80]) + (countLit q [-82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -76, -77, -80]) (l₂ := [-82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1590)) (countLit q [-73, -76, -77, -80]) (countLit q [-82, -84, -86, -89]) (count1587 q) 1 3 (meaning1575 q) (meaning1585 q) (meaning1590 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1585 = false ∨ valuation q 1590 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-73, -76, -77, -80]) + (countLit q [-82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -76, -77, -80]) (l₂ := [-82, -84, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1576)) (literal (valuationOf q) (1588)) (countLit q [-73, -76, -77, -80]) (countLit q [-82, -84, -86, -89]) (count1587 q) 2 (meaning1576 q) (meaning1588 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1588 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-73, -76, -77, -80]) + (countLit q [-82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -76, -77, -80]) (l₂ := [-82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1589)) (countLit q [-73, -76, -77, -80]) (countLit q [-82, -84, -86, -89]) (count1587 q) 2 1 (meaning1576 q) (meaning1583 q) (meaning1589 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1583 = false ∨ valuation q 1589 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1590 = true := by
  have hs : count1587 q = (countLit q [-73, -76, -77, -80]) + (countLit q [-82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -76, -77, -80]) (l₂ := [-82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1590)) (countLit q [-73, -76, -77, -80]) (countLit q [-82, -84, -86, -89]) (count1587 q) 2 2 (meaning1576 q) (meaning1584 q) (meaning1590 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1584 = false ∨ valuation q 1590 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1595 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1587)) (literal (valuationOf q) (1595)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 1 (meaning1587 q) (meaning1595 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1595 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1596 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1588)) (literal (valuationOf q) (1596)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 2 (meaning1588 q) (meaning1596 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1596 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1597 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1589)) (literal (valuationOf q) (1597)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 3 (meaning1589 q) (meaning1597 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1597 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E104.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112104
