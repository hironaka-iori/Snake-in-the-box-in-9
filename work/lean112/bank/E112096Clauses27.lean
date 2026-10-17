import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_right (literal (valuationOf q) (1621)) (literal (valuationOf q) (1625)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 3 (meaning1621 q) (meaning1625 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1625 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_right (literal (valuationOf q) (1622)) (literal (valuationOf q) (1626)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 4 (meaning1622 q) (meaning1626 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1626 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_left (literal (valuationOf q) (1612)) (literal (valuationOf q) (1623)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 1 (meaning1612 q) (meaning1623 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1623 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1624)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 1 1 (meaning1612 q) (meaning1619 q) (meaning1624 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1619 = false ∨ valuation q 1624 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1625)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 1 2 (meaning1612 q) (meaning1620 q) (meaning1625 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1620 = false ∨ valuation q 1625 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1626)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 1 3 (meaning1612 q) (meaning1621 q) (meaning1626 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1621 = false ∨ valuation q 1626 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1627 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1627)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 1 4 (meaning1612 q) (meaning1622 q) (meaning1627 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1622 = false ∨ valuation q 1627 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_left (literal (valuationOf q) (1613)) (literal (valuationOf q) (1624)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 2 (meaning1613 q) (meaning1624 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1624 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1625)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 2 1 (meaning1613 q) (meaning1619 q) (meaning1625 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1619 = false ∨ valuation q 1625 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1626)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 2 2 (meaning1613 q) (meaning1620 q) (meaning1626 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1620 = false ∨ valuation q 1626 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1627 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1627)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 2 3 (meaning1613 q) (meaning1621 q) (meaning1627 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1621 = false ∨ valuation q 1627 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_left (literal (valuationOf q) (1614)) (literal (valuationOf q) (1625)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 3 (meaning1614 q) (meaning1625 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1625 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1626)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 3 1 (meaning1614 q) (meaning1619 q) (meaning1626 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1619 = false ∨ valuation q 1626 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1627 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1627)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 3 2 (meaning1614 q) (meaning1620 q) (meaning1627 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1620 = false ∨ valuation q 1627 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1630)) (countLit q [-104]) (countLit q [-107]) (count1630 q) 1 (meaningNeg107 q) (meaning1630 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1630 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1630)) (countLit q [-104]) (countLit q [-107]) (count1630 q) 1 (meaningNeg104 q) (meaning1630 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1630 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1631 = true := by
  have hs : count1630 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1631)) (countLit q [-104]) (countLit q [-107]) (count1630 q) 1 1 (meaningNeg104 q) (meaningNeg107 q) (meaning1631 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 107 = true ∨ valuation q 1631 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-109]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-111])
  have hm := merge_right (literal (valuationOf q) (-111)) (literal (valuationOf q) (1632)) (countLit q [-109]) (countLit q [-111]) (count1632 q) 1 (meaningNeg111 q) (meaning1632 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1632 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-109]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-111])
  have hm := merge_left (literal (valuationOf q) (-109)) (literal (valuationOf q) (1632)) (countLit q [-109]) (countLit q [-111]) (count1632 q) 1 (meaningNeg109 q) (meaning1632 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1632 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 111 = true ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-109]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-111])
  have hm := merge_two (literal (valuationOf q) (-109)) (literal (valuationOf q) (-111)) (literal (valuationOf q) (1633)) (countLit q [-109]) (countLit q [-111]) (count1632 q) 1 1 (meaningNeg109 q) (meaningNeg111 q) (meaning1633 q) hs
  change (! (valuationOf q 109)) = false ∨ (! (valuationOf q 111)) = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 1633 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -111])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1634)) (countLit q [-104, -107]) (countLit q [-109, -111]) (count1634 q) 1 (meaning1632 q) (meaning1634 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1634 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -111])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1635)) (countLit q [-104, -107]) (countLit q [-109, -111]) (count1634 q) 2 (meaning1633 q) (meaning1635 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1635 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -111])
  have hm := merge_left (literal (valuationOf q) (1630)) (literal (valuationOf q) (1634)) (countLit q [-104, -107]) (countLit q [-109, -111]) (count1634 q) 1 (meaning1630 q) (meaning1634 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1634 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -111])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1635)) (countLit q [-104, -107]) (countLit q [-109, -111]) (count1634 q) 1 1 (meaning1630 q) (meaning1632 q) (meaning1635 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1632 = false ∨ valuation q 1635 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -111])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1636)) (countLit q [-104, -107]) (countLit q [-109, -111]) (count1634 q) 1 2 (meaning1630 q) (meaning1633 q) (meaning1636 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1633 = false ∨ valuation q 1636 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -111])
  have hm := merge_left (literal (valuationOf q) (1631)) (literal (valuationOf q) (1635)) (countLit q [-104, -107]) (countLit q [-109, -111]) (count1634 q) 2 (meaning1631 q) (meaning1635 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1635 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -111])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1636)) (countLit q [-104, -107]) (countLit q [-109, -111]) (count1634 q) 2 1 (meaning1631 q) (meaning1632 q) (meaning1636 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1632 = false ∨ valuation q 1636 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1637 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -111])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1637)) (countLit q [-104, -107]) (countLit q [-109, -111]) (count1634 q) 2 2 (meaning1631 q) (meaning1633 q) (meaning1637 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1633 = false ∨ valuation q 1637 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1638 = true := by
  have hs : count1638 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_right (literal (valuationOf q) (-114)) (literal (valuationOf q) (1638)) (countLit q [-113]) (countLit q [-114]) (count1638 q) 1 (meaningNeg114 q) (meaning1638 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1638 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1638 = true := by
  have hs : count1638 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_left (literal (valuationOf q) (-113)) (literal (valuationOf q) (1638)) (countLit q [-113]) (countLit q [-114]) (count1638 q) 1 (meaningNeg113 q) (meaning1638 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1638 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 114 = true ∨ valuationOf q 1639 = true := by
  have hs : count1638 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_two (literal (valuationOf q) (-113)) (literal (valuationOf q) (-114)) (literal (valuationOf q) (1639)) (countLit q [-113]) (countLit q [-114]) (count1638 q) 1 1 (meaningNeg113 q) (meaningNeg114 q) (meaning1639 q) hs
  change (! (valuationOf q 113)) = false ∨ (! (valuationOf q 114)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 1639 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1640 = true := by
  have hs : count1640 q = (countLit q [-116]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1640)) (countLit q [-116]) (countLit q [-117]) (count1640 q) 1 (meaningNeg117 q) (meaning1640 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1640 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E096.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112096
