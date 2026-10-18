import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true := by
  have hs : count1560 q = (countLit q [-63, -66]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-69, -70])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1562)) (countLit q [-63, -66]) (countLit q [-69, -70]) (count1560 q) 2 1 (meaning1557 q) (meaning1558 q) (meaning1562 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1558 = false ∨ valuation q 1562 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1563 = true := by
  have hs : count1560 q = (countLit q [-63, -66]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-69, -70])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1563)) (countLit q [-63, -66]) (countLit q [-69, -70]) (count1560 q) 2 2 (meaning1557 q) (meaning1559 q) (meaning1563 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1559 = false ∨ valuation q 1563 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -62]) + (countLit q [-63, -66, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-63, -66, -69, -70])
  have hm := merge_right (literal (valuationOf q) (1560)) (literal (valuationOf q) (1564)) (countLit q [-60, -61, -62]) (countLit q [-63, -66, -69, -70]) (count1564 q) 1 (meaning1560 q) (meaning1564 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1564 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -62]) + (countLit q [-63, -66, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-63, -66, -69, -70])
  have hm := merge_right (literal (valuationOf q) (1561)) (literal (valuationOf q) (1565)) (countLit q [-60, -61, -62]) (countLit q [-63, -66, -69, -70]) (count1564 q) 2 (meaning1561 q) (meaning1565 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1565 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -62]) + (countLit q [-63, -66, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-63, -66, -69, -70])
  have hm := merge_right (literal (valuationOf q) (1562)) (literal (valuationOf q) (1566)) (countLit q [-60, -61, -62]) (countLit q [-63, -66, -69, -70]) (count1564 q) 3 (meaning1562 q) (meaning1566 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1566 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1567 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -62]) + (countLit q [-63, -66, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-63, -66, -69, -70])
  have hm := merge_right (literal (valuationOf q) (1563)) (literal (valuationOf q) (1567)) (countLit q [-60, -61, -62]) (countLit q [-63, -66, -69, -70]) (count1564 q) 4 (meaning1563 q) (meaning1567 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1567 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -62]) + (countLit q [-63, -66, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-63, -66, -69, -70])
  have hm := merge_left (literal (valuationOf q) (1553)) (literal (valuationOf q) (1564)) (countLit q [-60, -61, -62]) (countLit q [-63, -66, -69, -70]) (count1564 q) 1 (meaning1553 q) (meaning1564 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1564 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -62]) + (countLit q [-63, -66, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-63, -66, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1565)) (countLit q [-60, -61, -62]) (countLit q [-63, -66, -69, -70]) (count1564 q) 1 1 (meaning1553 q) (meaning1560 q) (meaning1565 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1560 = false ∨ valuation q 1565 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -62]) + (countLit q [-63, -66, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-63, -66, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1566)) (countLit q [-60, -61, -62]) (countLit q [-63, -66, -69, -70]) (count1564 q) 1 2 (meaning1553 q) (meaning1561 q) (meaning1566 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1561 = false ∨ valuation q 1566 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1567 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -62]) + (countLit q [-63, -66, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-63, -66, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1567)) (countLit q [-60, -61, -62]) (countLit q [-63, -66, -69, -70]) (count1564 q) 1 3 (meaning1553 q) (meaning1562 q) (meaning1567 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1562 = false ∨ valuation q 1567 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -62]) + (countLit q [-63, -66, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-63, -66, -69, -70])
  have hm := merge_left (literal (valuationOf q) (1554)) (literal (valuationOf q) (1565)) (countLit q [-60, -61, -62]) (countLit q [-63, -66, -69, -70]) (count1564 q) 2 (meaning1554 q) (meaning1565 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1565 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -62]) + (countLit q [-63, -66, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-63, -66, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1566)) (countLit q [-60, -61, -62]) (countLit q [-63, -66, -69, -70]) (count1564 q) 2 1 (meaning1554 q) (meaning1560 q) (meaning1566 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1560 = false ∨ valuation q 1566 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1567 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -62]) + (countLit q [-63, -66, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-63, -66, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1567)) (countLit q [-60, -61, -62]) (countLit q [-63, -66, -69, -70]) (count1564 q) 2 2 (meaning1554 q) (meaning1561 q) (meaning1567 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1561 = false ∨ valuation q 1567 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -62]) + (countLit q [-63, -66, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-63, -66, -69, -70])
  have hm := merge_left (literal (valuationOf q) (1555)) (literal (valuationOf q) (1566)) (countLit q [-60, -61, -62]) (countLit q [-63, -66, -69, -70]) (count1564 q) 3 (meaning1555 q) (meaning1566 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1566 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1567 = true := by
  have hs : count1564 q = (countLit q [-60, -61, -62]) + (countLit q [-63, -66, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-63, -66, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1567)) (countLit q [-60, -61, -62]) (countLit q [-63, -66, -69, -70]) (count1564 q) 3 1 (meaning1555 q) (meaning1560 q) (meaning1567 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1560 = false ∨ valuation q 1567 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1571)) (countLit q [-72]) (countLit q [-73]) (count1571 q) 1 (meaningNeg73 q) (meaning1571 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1571 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1573)) (countLit q [-77]) (countLit q [-78]) (count1573 q) 1 (meaningNeg78 q) (meaning1573 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1573 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1573)) (countLit q [-77]) (countLit q [-78]) (count1573 q) 1 (meaningNeg77 q) (meaning1573 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1573 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 78 = true ∨ valuationOf q 1574 = true := by
  have hs : count1573 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-78)) (literal (valuationOf q) (1574)) (countLit q [-77]) (countLit q [-78]) (count1573 q) 1 1 (meaningNeg77 q) (meaningNeg78 q) (meaning1574 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 78)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 78 = true ∨ valuation q 1574 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-72, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (1573)) (literal (valuationOf q) (1575)) (countLit q [-72, -73]) (countLit q [-77, -78]) (count1575 q) 1 (meaning1573 q) (meaning1575 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1575 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-72, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (1574)) (literal (valuationOf q) (1576)) (countLit q [-72, -73]) (countLit q [-77, -78]) (count1575 q) 2 (meaning1574 q) (meaning1576 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1576 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-72, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (1571)) (literal (valuationOf q) (1575)) (countLit q [-72, -73]) (countLit q [-77, -78]) (count1575 q) 1 (meaning1571 q) (meaning1575 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1575 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-72, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1576)) (countLit q [-72, -73]) (countLit q [-77, -78]) (count1575 q) 1 1 (meaning1571 q) (meaning1573 q) (meaning1576 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1573 = false ∨ valuation q 1576 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1577 = true := by
  have hs : count1575 q = (countLit q [-72, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1577)) (countLit q [-72, -73]) (countLit q [-77, -78]) (count1575 q) 1 2 (meaning1571 q) (meaning1574 q) (meaning1577 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1574 = false ∨ valuation q 1577 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1579)) (countLit q [-80]) (countLit q [-81]) (count1579 q) 1 (meaningNeg81 q) (meaning1579 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1579 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1579)) (countLit q [-80]) (countLit q [-81]) (count1579 q) 1 (meaningNeg80 q) (meaning1579 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1579 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1580)) (countLit q [-80]) (countLit q [-81]) (count1579 q) 1 1 (meaningNeg80 q) (meaningNeg81 q) (meaning1580 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 1580 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1581 = true := by
  have hs : count1581 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1581)) (countLit q [-85]) (countLit q [-86]) (count1581 q) 1 (meaningNeg86 q) (meaning1581 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1581 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1581 = true := by
  have hs : count1581 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1581)) (countLit q [-85]) (countLit q [-86]) (count1581 q) 1 (meaningNeg85 q) (meaning1581 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1581 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1582 = true := by
  have hs : count1581 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1582)) (countLit q [-85]) (countLit q [-86]) (count1581 q) 1 1 (meaningNeg85 q) (meaningNeg86 q) (meaning1582 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 86 = true ∨ valuation q 1582 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-80, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1583)) (countLit q [-80, -81]) (countLit q [-85, -86]) (count1583 q) 1 (meaning1581 q) (meaning1583 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1583 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-80, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (1582)) (literal (valuationOf q) (1584)) (countLit q [-80, -81]) (countLit q [-85, -86]) (count1583 q) 2 (meaning1582 q) (meaning1584 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1584 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E096.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112096
