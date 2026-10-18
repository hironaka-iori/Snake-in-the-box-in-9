import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1640 = true := by
  have hs : count1640 q = (countLit q [-116]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-116)) (literal (valuationOf q) (1640)) (countLit q [-116]) (countLit q [-117]) (count1640 q) 1 (meaningNeg116 q) (meaning1640 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1640 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 117 = true ∨ valuationOf q 1641 = true := by
  have hs : count1640 q = (countLit q [-116]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-117])
  have hm := merge_two (literal (valuationOf q) (-116)) (literal (valuationOf q) (-117)) (literal (valuationOf q) (1641)) (countLit q [-116]) (countLit q [-117]) (count1640 q) 1 1 (meaningNeg116 q) (meaningNeg117 q) (meaning1641 q) hs
  change (! (valuationOf q 116)) = false ∨ (! (valuationOf q 117)) = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 117 = true ∨ valuation q 1641 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1642 = true := by
  have hs : count1642 q = (countLit q [-113, -114]) + (countLit q [-116, -117]) := List.countP_append (p := literal q) (l₁ := [-113, -114]) (l₂ := [-116, -117])
  have hm := merge_right (literal (valuationOf q) (1640)) (literal (valuationOf q) (1642)) (countLit q [-113, -114]) (countLit q [-116, -117]) (count1642 q) 1 (meaning1640 q) (meaning1642 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1642 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1643 = true := by
  have hs : count1642 q = (countLit q [-113, -114]) + (countLit q [-116, -117]) := List.countP_append (p := literal q) (l₁ := [-113, -114]) (l₂ := [-116, -117])
  have hm := merge_right (literal (valuationOf q) (1641)) (literal (valuationOf q) (1643)) (countLit q [-113, -114]) (countLit q [-116, -117]) (count1642 q) 2 (meaning1641 q) (meaning1643 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1643 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1642 = true := by
  have hs : count1642 q = (countLit q [-113, -114]) + (countLit q [-116, -117]) := List.countP_append (p := literal q) (l₁ := [-113, -114]) (l₂ := [-116, -117])
  have hm := merge_left (literal (valuationOf q) (1638)) (literal (valuationOf q) (1642)) (countLit q [-113, -114]) (countLit q [-116, -117]) (count1642 q) 1 (meaning1638 q) (meaning1642 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1642 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true := by
  have hs : count1642 q = (countLit q [-113, -114]) + (countLit q [-116, -117]) := List.countP_append (p := literal q) (l₁ := [-113, -114]) (l₂ := [-116, -117])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1643)) (countLit q [-113, -114]) (countLit q [-116, -117]) (count1642 q) 1 1 (meaning1638 q) (meaning1640 q) (meaning1643 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1640 = false ∨ valuation q 1643 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1644 = true := by
  have hs : count1642 q = (countLit q [-113, -114]) + (countLit q [-116, -117]) := List.countP_append (p := literal q) (l₁ := [-113, -114]) (l₂ := [-116, -117])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1644)) (countLit q [-113, -114]) (countLit q [-116, -117]) (count1642 q) 1 2 (meaning1638 q) (meaning1641 q) (meaning1644 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1641 = false ∨ valuation q 1644 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1643 = true := by
  have hs : count1642 q = (countLit q [-113, -114]) + (countLit q [-116, -117]) := List.countP_append (p := literal q) (l₁ := [-113, -114]) (l₂ := [-116, -117])
  have hm := merge_left (literal (valuationOf q) (1639)) (literal (valuationOf q) (1643)) (countLit q [-113, -114]) (countLit q [-116, -117]) (count1642 q) 2 (meaning1639 q) (meaning1643 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1643 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true := by
  have hs : count1642 q = (countLit q [-113, -114]) + (countLit q [-116, -117]) := List.countP_append (p := literal q) (l₁ := [-113, -114]) (l₂ := [-116, -117])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1644)) (countLit q [-113, -114]) (countLit q [-116, -117]) (count1642 q) 2 1 (meaning1639 q) (meaning1640 q) (meaning1644 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1640 = false ∨ valuation q 1644 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1642 q = (countLit q [-113, -114]) + (countLit q [-116, -117]) := List.countP_append (p := literal q) (l₁ := [-113, -114]) (l₂ := [-116, -117])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-113, -114]) (countLit q [-116, -117]) (count1642 q) 2 2 (meaning1639 q) (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = false ∨ valuation q 1645 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1646 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_right (literal (valuationOf q) (1642)) (literal (valuationOf q) (1646)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 1 (meaning1642 q) (meaning1646 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1646 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_right (literal (valuationOf q) (1643)) (literal (valuationOf q) (1647)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 2 (meaning1643 q) (meaning1647 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_right (literal (valuationOf q) (1644)) (literal (valuationOf q) (1648)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 3 (meaning1644 q) (meaning1648 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1648 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1646 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_left (literal (valuationOf q) (1634)) (literal (valuationOf q) (1646)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 1 (meaning1634 q) (meaning1646 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1646 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1647)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 1 1 (meaning1634 q) (meaning1642 q) (meaning1647 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1642 = false ∨ valuation q 1647 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1648)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 1 2 (meaning1634 q) (meaning1643 q) (meaning1648 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1643 = false ∨ valuation q 1648 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1649)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 1 3 (meaning1634 q) (meaning1644 q) (meaning1649 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1644 = false ∨ valuation q 1649 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1650)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 1 4 (meaning1634 q) (meaning1645 q) (meaning1650 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1645 = false ∨ valuation q 1650 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_left (literal (valuationOf q) (1635)) (literal (valuationOf q) (1647)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 2 (meaning1635 q) (meaning1647 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1647 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1648)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 2 1 (meaning1635 q) (meaning1642 q) (meaning1648 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1642 = false ∨ valuation q 1648 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1649)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 2 2 (meaning1635 q) (meaning1643 q) (meaning1649 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1643 = false ∨ valuation q 1649 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1650)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 2 3 (meaning1635 q) (meaning1644 q) (meaning1650 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1644 = false ∨ valuation q 1650 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1651)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 2 4 (meaning1635 q) (meaning1645 q) (meaning1651 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1645 = false ∨ valuation q 1651 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_left (literal (valuationOf q) (1636)) (literal (valuationOf q) (1648)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 3 (meaning1636 q) (meaning1648 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1648 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1649)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 3 1 (meaning1636 q) (meaning1642 q) (meaning1649 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1642 = false ∨ valuation q 1649 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1650)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 3 2 (meaning1636 q) (meaning1643 q) (meaning1650 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1643 = false ∨ valuation q 1650 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1651)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 3 3 (meaning1636 q) (meaning1644 q) (meaning1651 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1644 = false ∨ valuation q 1651 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1652 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1652)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 3 4 (meaning1636 q) (meaning1645 q) (meaning1652 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1645 = false ∨ valuation q 1652 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_left (literal (valuationOf q) (1637)) (literal (valuationOf q) (1649)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 4 (meaning1637 q) (meaning1649 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1649 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1650)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 4 1 (meaning1637 q) (meaning1642 q) (meaning1650 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1642 = false ∨ valuation q 1650 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1651)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 4 2 (meaning1637 q) (meaning1643 q) (meaning1651 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1643 = false ∨ valuation q 1651 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1652 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -111]) + (countLit q [-113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -111]) (l₂ := [-113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1652)) (countLit q [-104, -107, -109, -111]) (countLit q [-113, -114, -116, -117]) (count1646 q) 4 3 (meaning1637 q) (meaning1644 q) (meaning1652 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1644 = false ∨ valuation q 1652 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E096.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112096
