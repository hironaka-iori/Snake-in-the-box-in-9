import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1632)) (countLit q [-92]) (countLit q [-93]) (count1632 q) 1 (meaningNeg93 q) (meaning1632 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1632 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1632)) (countLit q [-92]) (countLit q [-93]) (count1632 q) 1 (meaningNeg92 q) (meaning1632 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1632 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1633)) (countLit q [-92]) (countLit q [-93]) (count1632 q) 1 1 (meaningNeg92 q) (meaningNeg93 q) (meaning1633 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 93 = true ∨ valuation q 1633 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1634)) (countLit q [-90]) (countLit q [-92, -93]) (count1634 q) 1 (meaning1632 q) (meaning1634 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1634 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1635)) (countLit q [-90]) (countLit q [-92, -93]) (count1634 q) 2 (meaning1633 q) (meaning1635 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1635 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1634)) (countLit q [-90]) (countLit q [-92, -93]) (count1634 q) 1 (meaningNeg90 q) (meaning1634 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1634 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1635)) (countLit q [-90]) (countLit q [-92, -93]) (count1634 q) 1 1 (meaningNeg90 q) (meaning1632 q) (meaning1635 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1632 = false ∨ valuation q 1635 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1636)) (countLit q [-90]) (countLit q [-92, -93]) (count1634 q) 1 2 (meaningNeg90 q) (meaning1633 q) (meaning1636 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1633 = false ∨ valuation q 1636 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1637)) (countLit q [-95]) (countLit q [-97]) (count1637 q) 1 (meaningNeg97 q) (meaning1637 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1637 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1637)) (countLit q [-95]) (countLit q [-97]) (count1637 q) 1 (meaningNeg95 q) (meaning1637 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1637 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 97 = true ∨ valuationOf q 1638 = true := by
  have hs : count1637 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (1638)) (countLit q [-95]) (countLit q [-97]) (count1637 q) 1 1 (meaningNeg95 q) (meaningNeg97 q) (meaning1638 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 1638 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1639)) (countLit q [-98]) (countLit q [-101]) (count1639 q) 1 (meaningNeg101 q) (meaning1639 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1639 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1639)) (countLit q [-98]) (countLit q [-101]) (count1639 q) 1 (meaningNeg98 q) (meaning1639 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1639 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1640 = true := by
  have hs : count1639 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1640)) (countLit q [-98]) (countLit q [-101]) (count1639 q) 1 1 (meaningNeg98 q) (meaningNeg101 q) (meaning1640 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 1640 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-95, -97]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -101])
  have hm := merge_right (literal (valuationOf q) (1639)) (literal (valuationOf q) (1641)) (countLit q [-95, -97]) (countLit q [-98, -101]) (count1641 q) 1 (meaning1639 q) (meaning1641 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-95, -97]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -101])
  have hm := merge_right (literal (valuationOf q) (1640)) (literal (valuationOf q) (1642)) (countLit q [-95, -97]) (countLit q [-98, -101]) (count1641 q) 2 (meaning1640 q) (meaning1642 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1642 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-95, -97]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -101])
  have hm := merge_left (literal (valuationOf q) (1637)) (literal (valuationOf q) (1641)) (countLit q [-95, -97]) (countLit q [-98, -101]) (count1641 q) 1 (meaning1637 q) (meaning1641 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1641 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-95, -97]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -101])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1642)) (countLit q [-95, -97]) (countLit q [-98, -101]) (count1641 q) 1 1 (meaning1637 q) (meaning1639 q) (meaning1642 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1639 = false ∨ valuation q 1642 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true := by
  have hs : count1641 q = (countLit q [-95, -97]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -101])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1643)) (countLit q [-95, -97]) (countLit q [-98, -101]) (count1641 q) 1 2 (meaning1637 q) (meaning1640 q) (meaning1643 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1640 = false ∨ valuation q 1643 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-95, -97]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -101])
  have hm := merge_left (literal (valuationOf q) (1638)) (literal (valuationOf q) (1642)) (countLit q [-95, -97]) (countLit q [-98, -101]) (count1641 q) 2 (meaning1638 q) (meaning1642 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1642 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1643 = true := by
  have hs : count1641 q = (countLit q [-95, -97]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -101])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1643)) (countLit q [-95, -97]) (countLit q [-98, -101]) (count1641 q) 2 1 (meaning1638 q) (meaning1639 q) (meaning1643 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1639 = false ∨ valuation q 1643 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true := by
  have hs : count1641 q = (countLit q [-95, -97]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -101])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1644)) (countLit q [-95, -97]) (countLit q [-98, -101]) (count1641 q) 2 2 (meaning1638 q) (meaning1640 q) (meaning1644 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1640 = false ∨ valuation q 1644 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_right (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 1 (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1645 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_right (literal (valuationOf q) (1642)) (literal (valuationOf q) (1646)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 2 (meaning1642 q) (meaning1646 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1646 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_right (literal (valuationOf q) (1643)) (literal (valuationOf q) (1647)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 3 (meaning1643 q) (meaning1647 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_right (literal (valuationOf q) (1644)) (literal (valuationOf q) (1648)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 4 (meaning1644 q) (meaning1648 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1648 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_left (literal (valuationOf q) (1634)) (literal (valuationOf q) (1645)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 1 (meaning1634 q) (meaning1645 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1645 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1646)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 1 1 (meaning1634 q) (meaning1641 q) (meaning1646 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1641 = false ∨ valuation q 1646 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1647)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 1 2 (meaning1634 q) (meaning1642 q) (meaning1647 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1642 = false ∨ valuation q 1647 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1648)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 1 3 (meaning1634 q) (meaning1643 q) (meaning1648 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1643 = false ∨ valuation q 1648 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1649)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 1 4 (meaning1634 q) (meaning1644 q) (meaning1649 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1644 = false ∨ valuation q 1649 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_left (literal (valuationOf q) (1635)) (literal (valuationOf q) (1646)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 2 (meaning1635 q) (meaning1646 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1646 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E187.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112187
