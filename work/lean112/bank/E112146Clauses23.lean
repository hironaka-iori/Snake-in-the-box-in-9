import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1550 = true := by
  have hs : count1549 q = (countLit q [-91, -94]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-91, -94]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1550)) (countLit q [-91, -94]) (countLit q [-95, -97]) (count1549 q) 1 1 (meaning1545 q) (meaning1547 q) (meaning1550 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1547 = false ∨ valuation q 1550 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1551 = true := by
  have hs : count1549 q = (countLit q [-91, -94]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-91, -94]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1551)) (countLit q [-91, -94]) (countLit q [-95, -97]) (count1549 q) 1 2 (meaning1545 q) (meaning1548 q) (meaning1551 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1548 = false ∨ valuation q 1551 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-86, -88, -90]) + (countLit q [-91, -94, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90]) (l₂ := [-91, -94, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1554)) (countLit q [-86, -88, -90]) (countLit q [-91, -94, -95, -97]) (count1553 q) 1 1 (meaning1542 q) (meaning1549 q) (meaning1554 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1549 = false ∨ valuation q 1554 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1555 = true := by
  have hs : count1553 q = (countLit q [-86, -88, -90]) + (countLit q [-91, -94, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90]) (l₂ := [-91, -94, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1555)) (countLit q [-86, -88, -90]) (countLit q [-91, -94, -95, -97]) (count1553 q) 1 2 (meaning1542 q) (meaning1550 q) (meaning1555 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1550 = false ∨ valuation q 1555 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1555 = true := by
  have hs : count1553 q = (countLit q [-86, -88, -90]) + (countLit q [-91, -94, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90]) (l₂ := [-91, -94, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1555)) (countLit q [-86, -88, -90]) (countLit q [-91, -94, -95, -97]) (count1553 q) 2 1 (meaning1543 q) (meaning1549 q) (meaning1555 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1549 = false ∨ valuation q 1555 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1556 = true := by
  have hs : count1553 q = (countLit q [-86, -88, -90]) + (countLit q [-91, -94, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90]) (l₂ := [-91, -94, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1556)) (countLit q [-86, -88, -90]) (countLit q [-91, -94, -95, -97]) (count1553 q) 2 2 (meaning1543 q) (meaning1550 q) (meaning1556 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1550 = false ∨ valuation q 1556 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1557 = true := by
  have hs : count1553 q = (countLit q [-86, -88, -90]) + (countLit q [-91, -94, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90]) (l₂ := [-91, -94, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1557)) (countLit q [-86, -88, -90]) (countLit q [-91, -94, -95, -97]) (count1553 q) 2 3 (meaning1543 q) (meaning1551 q) (meaning1557 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1551 = false ∨ valuation q 1557 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1556 = true := by
  have hs : count1553 q = (countLit q [-86, -88, -90]) + (countLit q [-91, -94, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90]) (l₂ := [-91, -94, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1556)) (countLit q [-86, -88, -90]) (countLit q [-91, -94, -95, -97]) (count1553 q) 3 1 (meaning1544 q) (meaning1549 q) (meaning1556 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1549 = false ∨ valuation q 1556 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1557 = true := by
  have hs : count1553 q = (countLit q [-86, -88, -90]) + (countLit q [-91, -94, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90]) (l₂ := [-91, -94, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1557)) (countLit q [-86, -88, -90]) (countLit q [-91, -94, -95, -97]) (count1553 q) 3 2 (meaning1544 q) (meaning1550 q) (meaning1557 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1550 = false ∨ valuation q 1557 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1558 = true := by
  have hs : count1553 q = (countLit q [-86, -88, -90]) + (countLit q [-91, -94, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90]) (l₂ := [-91, -94, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1558)) (countLit q [-86, -88, -90]) (countLit q [-91, -94, -95, -97]) (count1553 q) 3 3 (meaning1544 q) (meaning1551 q) (meaning1558 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1551 = false ∨ valuation q 1558 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1560)) (countLit q [-99]) (countLit q [-101]) (count1560 q) 1 (meaningNeg101 q) (meaning1560 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1560 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1560)) (countLit q [-99]) (countLit q [-101]) (count1560 q) 1 (meaningNeg99 q) (meaning1560 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1560 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1562 = true := by
  have hs : count1562 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1562)) (countLit q [-104]) (countLit q [-106]) (count1562 q) 1 (meaningNeg106 q) (meaning1562 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1562 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1562 = true := by
  have hs : count1562 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1562)) (countLit q [-104]) (countLit q [-106]) (count1562 q) 1 (meaningNeg104 q) (meaning1562 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1562 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 106 = true ∨ valuationOf q 1563 = true := by
  have hs : count1562 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-106)) (literal (valuationOf q) (1563)) (countLit q [-104]) (countLit q [-106]) (count1562 q) 1 1 (meaningNeg104 q) (meaningNeg106 q) (meaning1563 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 106)) = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 1563 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-99, -101]) + (countLit q [-104, -106]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-104, -106])
  have hm := merge_right (literal (valuationOf q) (1562)) (literal (valuationOf q) (1564)) (countLit q [-99, -101]) (countLit q [-104, -106]) (count1564 q) 1 (meaning1562 q) (meaning1564 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1564 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-99, -101]) + (countLit q [-104, -106]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-104, -106])
  have hm := merge_right (literal (valuationOf q) (1563)) (literal (valuationOf q) (1565)) (countLit q [-99, -101]) (countLit q [-104, -106]) (count1564 q) 2 (meaning1563 q) (meaning1565 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1565 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-99, -101]) + (countLit q [-104, -106]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-104, -106])
  have hm := merge_left (literal (valuationOf q) (1560)) (literal (valuationOf q) (1564)) (countLit q [-99, -101]) (countLit q [-104, -106]) (count1564 q) 1 (meaning1560 q) (meaning1564 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1564 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-99, -101]) + (countLit q [-104, -106]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-104, -106])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1565)) (countLit q [-99, -101]) (countLit q [-104, -106]) (count1564 q) 1 1 (meaning1560 q) (meaning1562 q) (meaning1565 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1562 = false ∨ valuation q 1565 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1568 = true := by
  have hs : count1568 q = (countLit q [-108]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-109])
  have hm := merge_right (literal (valuationOf q) (-109)) (literal (valuationOf q) (1568)) (countLit q [-108]) (countLit q [-109]) (count1568 q) 1 (meaningNeg109 q) (meaning1568 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1568 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1570 = true := by
  have hs : count1570 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1570)) (countLit q [-112]) (countLit q [-113]) (count1570 q) 1 (meaningNeg113 q) (meaning1570 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1570 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1572 = true := by
  have hs : count1572 q = (countLit q [-108, -109]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-108, -109]) (l₂ := [-112, -113])
  have hm := merge_right (literal (valuationOf q) (1570)) (literal (valuationOf q) (1572)) (countLit q [-108, -109]) (countLit q [-112, -113]) (count1572 q) 1 (meaning1570 q) (meaning1572 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1572 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1572 = true := by
  have hs : count1572 q = (countLit q [-108, -109]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-108, -109]) (l₂ := [-112, -113])
  have hm := merge_left (literal (valuationOf q) (1568)) (literal (valuationOf q) (1572)) (countLit q [-108, -109]) (countLit q [-112, -113]) (count1572 q) 1 (meaning1568 q) (meaning1572 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1572 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-99, -101, -104, -106]) + (countLit q [-108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -104, -106]) (l₂ := [-108, -109, -112, -113])
  have hm := merge_right (literal (valuationOf q) (1572)) (literal (valuationOf q) (1576)) (countLit q [-99, -101, -104, -106]) (countLit q [-108, -109, -112, -113]) (count1576 q) 1 (meaning1572 q) (meaning1576 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1576 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-99, -101, -104, -106]) + (countLit q [-108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -104, -106]) (l₂ := [-108, -109, -112, -113])
  have hm := merge_left (literal (valuationOf q) (1564)) (literal (valuationOf q) (1576)) (countLit q [-99, -101, -104, -106]) (countLit q [-108, -109, -112, -113]) (count1576 q) 1 (meaning1564 q) (meaning1576 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1576 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1577 = true := by
  have hs : count1576 q = (countLit q [-99, -101, -104, -106]) + (countLit q [-108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -104, -106]) (l₂ := [-108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1577)) (countLit q [-99, -101, -104, -106]) (countLit q [-108, -109, -112, -113]) (count1576 q) 1 1 (meaning1564 q) (meaning1572 q) (meaning1577 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1572 = false ∨ valuation q 1577 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1577 = true := by
  have hs : count1576 q = (countLit q [-99, -101, -104, -106]) + (countLit q [-108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -104, -106]) (l₂ := [-108, -109, -112, -113])
  have hm := merge_left (literal (valuationOf q) (1565)) (literal (valuationOf q) (1577)) (countLit q [-99, -101, -104, -106]) (countLit q [-108, -109, -112, -113]) (count1576 q) 2 (meaning1565 q) (meaning1577 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1577 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1586 = true := by
  have hs : count1584 q = (countLit q [-86, -88, -90, -91, -94, -95, -97]) + (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90, -91, -94, -95, -97]) (l₂ := [-99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1586)) (countLit q [-86, -88, -90, -91, -94, -95, -97]) (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) (count1584 q) 2 1 (meaning1554 q) (meaning1576 q) (meaning1586 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1576 = false ∨ valuation q 1586 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1587 = true := by
  have hs : count1584 q = (countLit q [-86, -88, -90, -91, -94, -95, -97]) + (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90, -91, -94, -95, -97]) (l₂ := [-99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1587)) (countLit q [-86, -88, -90, -91, -94, -95, -97]) (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) (count1584 q) 2 2 (meaning1554 q) (meaning1577 q) (meaning1587 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1577 = false ∨ valuation q 1587 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1587 = true := by
  have hs : count1584 q = (countLit q [-86, -88, -90, -91, -94, -95, -97]) + (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90, -91, -94, -95, -97]) (l₂ := [-99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1587)) (countLit q [-86, -88, -90, -91, -94, -95, -97]) (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) (count1584 q) 3 1 (meaning1555 q) (meaning1576 q) (meaning1587 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1576 = false ∨ valuation q 1587 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1588 = true := by
  have hs : count1584 q = (countLit q [-86, -88, -90, -91, -94, -95, -97]) + (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90, -91, -94, -95, -97]) (l₂ := [-99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1588)) (countLit q [-86, -88, -90, -91, -94, -95, -97]) (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) (count1584 q) 3 2 (meaning1555 q) (meaning1577 q) (meaning1588 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1577 = false ∨ valuation q 1588 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1588 = true := by
  have hs : count1584 q = (countLit q [-86, -88, -90, -91, -94, -95, -97]) + (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90, -91, -94, -95, -97]) (l₂ := [-99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1588)) (countLit q [-86, -88, -90, -91, -94, -95, -97]) (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) (count1584 q) 4 1 (meaning1556 q) (meaning1576 q) (meaning1588 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1576 = false ∨ valuation q 1588 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E146.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112146
