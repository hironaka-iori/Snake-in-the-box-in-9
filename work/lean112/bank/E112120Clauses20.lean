import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1546 = true := by
  have hs : count1546 q = (countLit q [-73]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1546)) (countLit q [-73]) (countLit q [-77]) (count1546 q) 1 (meaningNeg73 q) (meaning1546 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1546 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1547 = true := by
  have hs : count1546 q = (countLit q [-73]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-73)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1547)) (countLit q [-73]) (countLit q [-77]) (count1546 q) 1 1 (meaningNeg73 q) (meaningNeg77 q) (meaning1547 q) hs
  change (! (valuationOf q 73)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 77 = true ∨ valuation q 1547 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1548 = true := by
  have hs : count1548 q = (countLit q [-72]) + (countLit q [-73, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -77])
  have hm := merge_right (literal (valuationOf q) (1546)) (literal (valuationOf q) (1548)) (countLit q [-72]) (countLit q [-73, -77]) (count1548 q) 1 (meaning1546 q) (meaning1548 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1548 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1549 = true := by
  have hs : count1548 q = (countLit q [-72]) + (countLit q [-73, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -77])
  have hm := merge_right (literal (valuationOf q) (1547)) (literal (valuationOf q) (1549)) (countLit q [-72]) (countLit q [-73, -77]) (count1548 q) 2 (meaning1547 q) (meaning1549 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1549 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1548 = true := by
  have hs : count1548 q = (countLit q [-72]) + (countLit q [-73, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -77])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1548)) (countLit q [-72]) (countLit q [-73, -77]) (count1548 q) 1 (meaningNeg72 q) (meaning1548 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1548 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1546 = false ∨ valuationOf q 1549 = true := by
  have hs : count1548 q = (countLit q [-72]) + (countLit q [-73, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -77])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1549)) (countLit q [-72]) (countLit q [-73, -77]) (count1548 q) 1 1 (meaningNeg72 q) (meaning1546 q) (meaning1549 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1546 = false ∨ valuation q 1549 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1547 = false ∨ valuationOf q 1550 = true := by
  have hs : count1548 q = (countLit q [-72]) + (countLit q [-73, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -77])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1550)) (countLit q [-72]) (countLit q [-73, -77]) (count1548 q) 1 2 (meaningNeg72 q) (meaning1547 q) (meaning1550 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1547 = false ∨ valuation q 1550 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1551)) (countLit q [-78]) (countLit q [-81]) (count1551 q) 1 (meaningNeg81 q) (meaning1551 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1551 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1551)) (countLit q [-78]) (countLit q [-81]) (count1551 q) 1 (meaningNeg78 q) (meaning1551 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1551 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1552 = true := by
  have hs : count1551 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1552)) (countLit q [-78]) (countLit q [-81]) (count1551 q) 1 1 (meaningNeg78 q) (meaningNeg81 q) (meaning1552 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 81 = true ∨ valuation q 1552 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1553)) (countLit q [-85]) (countLit q [-86]) (count1553 q) 1 (meaningNeg86 q) (meaning1553 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1553 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1553)) (countLit q [-85]) (countLit q [-86]) (count1553 q) 1 (meaningNeg85 q) (meaning1553 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1553 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1554)) (countLit q [-85]) (countLit q [-86]) (count1553 q) 1 1 (meaningNeg85 q) (meaningNeg86 q) (meaning1554 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 86 = true ∨ valuation q 1554 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-78, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (1553)) (literal (valuationOf q) (1555)) (countLit q [-78, -81]) (countLit q [-85, -86]) (count1555 q) 1 (meaning1553 q) (meaning1555 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1555 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-78, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (1554)) (literal (valuationOf q) (1556)) (countLit q [-78, -81]) (countLit q [-85, -86]) (count1555 q) 2 (meaning1554 q) (meaning1556 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1556 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-78, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-85, -86])
  have hm := merge_left (literal (valuationOf q) (1551)) (literal (valuationOf q) (1555)) (countLit q [-78, -81]) (countLit q [-85, -86]) (count1555 q) 1 (meaning1551 q) (meaning1555 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1555 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-78, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1556)) (countLit q [-78, -81]) (countLit q [-85, -86]) (count1555 q) 1 1 (meaning1551 q) (meaning1553 q) (meaning1556 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1553 = false ∨ valuation q 1556 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1557 = true := by
  have hs : count1555 q = (countLit q [-78, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1557)) (countLit q [-78, -81]) (countLit q [-85, -86]) (count1555 q) 1 2 (meaning1551 q) (meaning1554 q) (meaning1557 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1554 = false ∨ valuation q 1557 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-78, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-85, -86])
  have hm := merge_left (literal (valuationOf q) (1552)) (literal (valuationOf q) (1556)) (countLit q [-78, -81]) (countLit q [-85, -86]) (count1555 q) 2 (meaning1552 q) (meaning1556 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1556 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1557 = true := by
  have hs : count1555 q = (countLit q [-78, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1557)) (countLit q [-78, -81]) (countLit q [-85, -86]) (count1555 q) 2 1 (meaning1552 q) (meaning1553 q) (meaning1557 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1553 = false ∨ valuation q 1557 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1558 = true := by
  have hs : count1555 q = (countLit q [-78, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1558)) (countLit q [-78, -81]) (countLit q [-85, -86]) (count1555 q) 2 2 (meaning1552 q) (meaning1554 q) (meaning1558 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1554 = false ∨ valuation q 1558 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1559 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_right (literal (valuationOf q) (1555)) (literal (valuationOf q) (1559)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 1 (meaning1555 q) (meaning1559 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1559 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_right (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 2 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1561 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_right (literal (valuationOf q) (1557)) (literal (valuationOf q) (1561)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 3 (meaning1557 q) (meaning1561 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1561 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1562 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_right (literal (valuationOf q) (1558)) (literal (valuationOf q) (1562)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 4 (meaning1558 q) (meaning1562 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1562 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1559 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_left (literal (valuationOf q) (1548)) (literal (valuationOf q) (1559)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 1 (meaning1548 q) (meaning1559 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1559 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1560)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 1 1 (meaning1548 q) (meaning1555 q) (meaning1560 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1555 = false ∨ valuation q 1560 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1561 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1561)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 1 2 (meaning1548 q) (meaning1556 q) (meaning1561 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1556 = false ∨ valuation q 1561 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1562 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1562)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 1 3 (meaning1548 q) (meaning1557 q) (meaning1562 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1557 = false ∨ valuation q 1562 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1563 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1563)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 1 4 (meaning1548 q) (meaning1558 q) (meaning1563 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1558 = false ∨ valuation q 1563 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_left (literal (valuationOf q) (1549)) (literal (valuationOf q) (1560)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 2 (meaning1549 q) (meaning1560 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1560 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1561 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1561)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 2 1 (meaning1549 q) (meaning1555 q) (meaning1561 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1555 = false ∨ valuation q 1561 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E120.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112120
