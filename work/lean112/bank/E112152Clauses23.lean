import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-81]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1617)) (countLit q [-81]) (countLit q [-84]) (count1617 q) 1 (meaningNeg81 q) (meaning1617 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1617 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 84 = true ∨ valuationOf q 1618 = true := by
  have hs : count1617 q = (countLit q [-81]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (1618)) (countLit q [-81]) (countLit q [-84]) (count1617 q) 1 1 (meaningNeg81 q) (meaningNeg84 q) (meaning1618 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 84 = true ∨ valuation q 1618 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-86]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1619)) (countLit q [-86]) (countLit q [-88]) (count1619 q) 1 (meaningNeg88 q) (meaning1619 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1619 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-86]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1619)) (countLit q [-86]) (countLit q [-88]) (count1619 q) 1 (meaningNeg86 q) (meaning1619 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1619 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 88 = true ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-86]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (1620)) (countLit q [-86]) (countLit q [-88]) (count1619 q) 1 1 (meaningNeg86 q) (meaningNeg88 q) (meaning1620 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 1620 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1621 = true := by
  have hs : count1621 q = (countLit q [-81, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-81, -84]) (l₂ := [-86, -88])
  have hm := merge_right (literal (valuationOf q) (1619)) (literal (valuationOf q) (1621)) (countLit q [-81, -84]) (countLit q [-86, -88]) (count1621 q) 1 (meaning1619 q) (meaning1621 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1621 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1622 = true := by
  have hs : count1621 q = (countLit q [-81, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-81, -84]) (l₂ := [-86, -88])
  have hm := merge_right (literal (valuationOf q) (1620)) (literal (valuationOf q) (1622)) (countLit q [-81, -84]) (countLit q [-86, -88]) (count1621 q) 2 (meaning1620 q) (meaning1622 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1622 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1621 = true := by
  have hs : count1621 q = (countLit q [-81, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-81, -84]) (l₂ := [-86, -88])
  have hm := merge_left (literal (valuationOf q) (1617)) (literal (valuationOf q) (1621)) (countLit q [-81, -84]) (countLit q [-86, -88]) (count1621 q) 1 (meaning1617 q) (meaning1621 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1621 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1622 = true := by
  have hs : count1621 q = (countLit q [-81, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-81, -84]) (l₂ := [-86, -88])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1622)) (countLit q [-81, -84]) (countLit q [-86, -88]) (count1621 q) 1 1 (meaning1617 q) (meaning1619 q) (meaning1622 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1619 = false ∨ valuation q 1622 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1623 = true := by
  have hs : count1621 q = (countLit q [-81, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-81, -84]) (l₂ := [-86, -88])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1623)) (countLit q [-81, -84]) (countLit q [-86, -88]) (count1621 q) 1 2 (meaning1617 q) (meaning1620 q) (meaning1623 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1620 = false ∨ valuation q 1623 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1622 = true := by
  have hs : count1621 q = (countLit q [-81, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-81, -84]) (l₂ := [-86, -88])
  have hm := merge_left (literal (valuationOf q) (1618)) (literal (valuationOf q) (1622)) (countLit q [-81, -84]) (countLit q [-86, -88]) (count1621 q) 2 (meaning1618 q) (meaning1622 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1622 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1623 = true := by
  have hs : count1621 q = (countLit q [-81, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-81, -84]) (l₂ := [-86, -88])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1623)) (countLit q [-81, -84]) (countLit q [-86, -88]) (count1621 q) 2 1 (meaning1618 q) (meaning1619 q) (meaning1623 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1619 = false ∨ valuation q 1623 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1624 = true := by
  have hs : count1621 q = (countLit q [-81, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-81, -84]) (l₂ := [-86, -88])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1624)) (countLit q [-81, -84]) (countLit q [-86, -88]) (count1621 q) 2 2 (meaning1618 q) (meaning1620 q) (meaning1624 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1620 = false ∨ valuation q 1624 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-74, -76, -79, -80]) + (countLit q [-81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80]) (l₂ := [-81, -84, -86, -88])
  have hm := merge_right (literal (valuationOf q) (1621)) (literal (valuationOf q) (1625)) (countLit q [-74, -76, -79, -80]) (countLit q [-81, -84, -86, -88]) (count1625 q) 1 (meaning1621 q) (meaning1625 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1625 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-74, -76, -79, -80]) + (countLit q [-81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80]) (l₂ := [-81, -84, -86, -88])
  have hm := merge_right (literal (valuationOf q) (1622)) (literal (valuationOf q) (1626)) (countLit q [-74, -76, -79, -80]) (countLit q [-81, -84, -86, -88]) (count1625 q) 2 (meaning1622 q) (meaning1626 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1626 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1627 = true := by
  have hs : count1625 q = (countLit q [-74, -76, -79, -80]) + (countLit q [-81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80]) (l₂ := [-81, -84, -86, -88])
  have hm := merge_right (literal (valuationOf q) (1623)) (literal (valuationOf q) (1627)) (countLit q [-74, -76, -79, -80]) (countLit q [-81, -84, -86, -88]) (count1625 q) 3 (meaning1623 q) (meaning1627 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1627 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1628 = true := by
  have hs : count1625 q = (countLit q [-74, -76, -79, -80]) + (countLit q [-81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80]) (l₂ := [-81, -84, -86, -88])
  have hm := merge_right (literal (valuationOf q) (1624)) (literal (valuationOf q) (1628)) (countLit q [-74, -76, -79, -80]) (countLit q [-81, -84, -86, -88]) (count1625 q) 4 (meaning1624 q) (meaning1628 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1628 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-74, -76, -79, -80]) + (countLit q [-81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80]) (l₂ := [-81, -84, -86, -88])
  have hm := merge_left (literal (valuationOf q) (1613)) (literal (valuationOf q) (1625)) (countLit q [-74, -76, -79, -80]) (countLit q [-81, -84, -86, -88]) (count1625 q) 1 (meaning1613 q) (meaning1625 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1625 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-74, -76, -79, -80]) + (countLit q [-81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80]) (l₂ := [-81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1626)) (countLit q [-74, -76, -79, -80]) (countLit q [-81, -84, -86, -88]) (count1625 q) 1 1 (meaning1613 q) (meaning1621 q) (meaning1626 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1621 = false ∨ valuation q 1626 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1627 = true := by
  have hs : count1625 q = (countLit q [-74, -76, -79, -80]) + (countLit q [-81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80]) (l₂ := [-81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1627)) (countLit q [-74, -76, -79, -80]) (countLit q [-81, -84, -86, -88]) (count1625 q) 1 2 (meaning1613 q) (meaning1622 q) (meaning1627 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1622 = false ∨ valuation q 1627 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1628 = true := by
  have hs : count1625 q = (countLit q [-74, -76, -79, -80]) + (countLit q [-81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80]) (l₂ := [-81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1628)) (countLit q [-74, -76, -79, -80]) (countLit q [-81, -84, -86, -88]) (count1625 q) 1 3 (meaning1613 q) (meaning1623 q) (meaning1628 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1623 = false ∨ valuation q 1628 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-74, -76, -79, -80]) + (countLit q [-81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80]) (l₂ := [-81, -84, -86, -88])
  have hm := merge_left (literal (valuationOf q) (1614)) (literal (valuationOf q) (1626)) (countLit q [-74, -76, -79, -80]) (countLit q [-81, -84, -86, -88]) (count1625 q) 2 (meaning1614 q) (meaning1626 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1626 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1627 = true := by
  have hs : count1625 q = (countLit q [-74, -76, -79, -80]) + (countLit q [-81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80]) (l₂ := [-81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1627)) (countLit q [-74, -76, -79, -80]) (countLit q [-81, -84, -86, -88]) (count1625 q) 2 1 (meaning1614 q) (meaning1621 q) (meaning1627 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1621 = false ∨ valuation q 1627 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1628 = true := by
  have hs : count1625 q = (countLit q [-74, -76, -79, -80]) + (countLit q [-81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80]) (l₂ := [-81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1628)) (countLit q [-74, -76, -79, -80]) (countLit q [-81, -84, -86, -88]) (count1625 q) 2 2 (meaning1614 q) (meaning1622 q) (meaning1628 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1622 = false ∨ valuation q 1628 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1628 = true := by
  have hs : count1625 q = (countLit q [-74, -76, -79, -80]) + (countLit q [-81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80]) (l₂ := [-81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1628)) (countLit q [-74, -76, -79, -80]) (countLit q [-81, -84, -86, -88]) (count1625 q) 3 1 (meaning1615 q) (meaning1621 q) (meaning1628 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1621 = false ∨ valuation q 1628 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1634 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1634)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 1 1 (meaning1602 q) (meaning1625 q) (meaning1634 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1625 = false ∨ valuation q 1634 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1635 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1635)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 1 2 (meaning1602 q) (meaning1626 q) (meaning1635 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1626 = false ∨ valuation q 1635 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1636 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1636)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 1 3 (meaning1602 q) (meaning1627 q) (meaning1636 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1627 = false ∨ valuation q 1636 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1637 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1637)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 1 4 (meaning1602 q) (meaning1628 q) (meaning1637 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1628 = false ∨ valuation q 1637 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1635 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1635)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 2 1 (meaning1603 q) (meaning1625 q) (meaning1635 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1625 = false ∨ valuation q 1635 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1636 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1636)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 2 2 (meaning1603 q) (meaning1626 q) (meaning1636 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1626 = false ∨ valuation q 1636 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1637 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1637)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 2 3 (meaning1603 q) (meaning1627 q) (meaning1637 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1627 = false ∨ valuation q 1637 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E152.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112152
