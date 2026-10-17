import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1562 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1562)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 2 2 (meaning1549 q) (meaning1556 q) (meaning1562 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1556 = false ∨ valuation q 1562 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1563 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1563)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 2 3 (meaning1549 q) (meaning1557 q) (meaning1563 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1557 = false ∨ valuation q 1563 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1562 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1562)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 3 1 (meaning1550 q) (meaning1555 q) (meaning1562 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1555 = false ∨ valuation q 1562 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1563 = true := by
  have hs : count1559 q = (countLit q [-72, -73, -77]) + (countLit q [-78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77]) (l₂ := [-78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1563)) (countLit q [-72, -73, -77]) (countLit q [-78, -81, -85, -86]) (count1559 q) 3 2 (meaning1550 q) (meaning1556 q) (meaning1563 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1556 = false ∨ valuation q 1563 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1568 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1568)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 1 2 (meaning1539 q) (meaning1560 q) (meaning1568 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1560 = false ∨ valuation q 1568 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1569)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 1 3 (meaning1539 q) (meaning1561 q) (meaning1569 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1561 = false ∨ valuation q 1569 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1570)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 1 4 (meaning1539 q) (meaning1562 q) (meaning1570 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1562 = false ∨ valuation q 1570 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1571 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1563)) (literal (valuationOf q) (1571)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 1 5 (meaning1539 q) (meaning1563 q) (meaning1571 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1563 = false ∨ valuation q 1571 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1568 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1568)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 2 1 (meaning1540 q) (meaning1559 q) (meaning1568 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1559 = false ∨ valuation q 1568 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1569)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 2 2 (meaning1540 q) (meaning1560 q) (meaning1569 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1560 = false ∨ valuation q 1569 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1570)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 2 3 (meaning1540 q) (meaning1561 q) (meaning1570 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1561 = false ∨ valuation q 1570 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1571 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1571)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 2 4 (meaning1540 q) (meaning1562 q) (meaning1571 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1562 = false ∨ valuation q 1571 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1572 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1563)) (literal (valuationOf q) (1572)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 2 5 (meaning1540 q) (meaning1563 q) (meaning1572 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1563 = false ∨ valuation q 1572 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1569)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 3 1 (meaning1541 q) (meaning1559 q) (meaning1569 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1559 = false ∨ valuation q 1569 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1570)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 3 2 (meaning1541 q) (meaning1560 q) (meaning1570 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1560 = false ∨ valuation q 1570 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1571 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1571)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 3 3 (meaning1541 q) (meaning1561 q) (meaning1571 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1561 = false ∨ valuation q 1571 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1572 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1572)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 3 4 (meaning1541 q) (meaning1562 q) (meaning1572 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1562 = false ∨ valuation q 1572 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1563)) (literal (valuationOf q) (1573)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 3 5 (meaning1541 q) (meaning1563 q) (meaning1573 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1563 = false ∨ valuation q 1573 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1570)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 4 1 (meaning1542 q) (meaning1559 q) (meaning1570 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1559 = false ∨ valuation q 1570 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1571 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1571)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 4 2 (meaning1542 q) (meaning1560 q) (meaning1571 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1560 = false ∨ valuation q 1571 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1572 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1572)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 4 3 (meaning1542 q) (meaning1561 q) (meaning1572 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1561 = false ∨ valuation q 1572 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1573)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 4 4 (meaning1542 q) (meaning1562 q) (meaning1573 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1562 = false ∨ valuation q 1573 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1572 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1572)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 5 2 (meaning1543 q) (meaning1560 q) (meaning1572 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1560 = false ∨ valuation q 1572 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1573)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 5 3 (meaning1543 q) (meaning1561 q) (meaning1573 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1561 = false ∨ valuation q 1573 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1574 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1574)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 5 4 (meaning1543 q) (meaning1562 q) (meaning1574 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1562 = false ∨ valuation q 1574 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1572 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1572)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 6 1 (meaning1544 q) (meaning1559 q) (meaning1572 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1559 = false ∨ valuation q 1572 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1573)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 6 2 (meaning1544 q) (meaning1560 q) (meaning1573 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1560 = false ∨ valuation q 1573 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-59, -62, -63, -64, -66, -70, -71]) + (countLit q [-72, -73, -77, -78, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71]) (l₂ := [-72, -73, -77, -78, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1573)) (countLit q [-59, -62, -63, -64, -66, -70, -71]) (countLit q [-72, -73, -77, -78, -81, -85, -86]) (count1566 q) 7 1 (meaning1545 q) (meaning1559 q) (meaning1573 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1559 = false ∨ valuation q 1573 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-91]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92])
  have hm := merge_right (literal (valuationOf q) (-92)) (literal (valuationOf q) (1580)) (countLit q [-91]) (countLit q [-92]) (count1580 q) 1 (meaningNeg92 q) (meaning1580 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1580 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-91]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1580)) (countLit q [-91]) (countLit q [-92]) (count1580 q) 1 (meaningNeg91 q) (meaning1580 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1580 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 92 = true ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-91]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (-92)) (literal (valuationOf q) (1581)) (countLit q [-91]) (countLit q [-92]) (count1580 q) 1 1 (meaningNeg91 q) (meaningNeg92 q) (meaning1581 q) hs
  change (! (valuationOf q 91)) = false ∨ (! (valuationOf q 92)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 92 = true ∨ valuation q 1581 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-88]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91, -92])
  have hm := merge_right (literal (valuationOf q) (1580)) (literal (valuationOf q) (1582)) (countLit q [-88]) (countLit q [-91, -92]) (count1582 q) 1 (meaning1580 q) (meaning1582 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1582 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E120.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112120
