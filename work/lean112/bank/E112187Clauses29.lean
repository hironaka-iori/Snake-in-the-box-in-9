import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1666 = true := by
  have hs : count1664 q = (countLit q [-111, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1666)) (countLit q [-111, -114]) (countLit q [-115, -117]) (count1664 q) 2 1 (meaning1661 q) (meaning1662 q) (meaning1666 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1662 = false ∨ valuation q 1666 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1667 = true := by
  have hs : count1664 q = (countLit q [-111, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1667)) (countLit q [-111, -114]) (countLit q [-115, -117]) (count1664 q) 2 2 (meaning1661 q) (meaning1663 q) (meaning1667 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1663 = false ∨ valuation q 1667 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1669 = true := by
  have hs : count1668 q = (countLit q [-104, -107, -108, -109]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -108, -109]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1665)) (literal (valuationOf q) (1669)) (countLit q [-104, -107, -108, -109]) (countLit q [-111, -114, -115, -117]) (count1668 q) 2 (meaning1665 q) (meaning1669 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1669 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1670 = true := by
  have hs : count1668 q = (countLit q [-104, -107, -108, -109]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -108, -109]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1666)) (literal (valuationOf q) (1670)) (countLit q [-104, -107, -108, -109]) (countLit q [-111, -114, -115, -117]) (count1668 q) 3 (meaning1666 q) (meaning1670 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1670 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1671 = true := by
  have hs : count1668 q = (countLit q [-104, -107, -108, -109]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -108, -109]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1667)) (literal (valuationOf q) (1671)) (countLit q [-104, -107, -108, -109]) (countLit q [-111, -114, -115, -117]) (count1668 q) 4 (meaning1667 q) (meaning1671 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1671 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1669 = true := by
  have hs : count1668 q = (countLit q [-104, -107, -108, -109]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -108, -109]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1669)) (countLit q [-104, -107, -108, -109]) (countLit q [-111, -114, -115, -117]) (count1668 q) 1 1 (meaning1656 q) (meaning1664 q) (meaning1669 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1664 = false ∨ valuation q 1669 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1670 = true := by
  have hs : count1668 q = (countLit q [-104, -107, -108, -109]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -108, -109]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1670)) (countLit q [-104, -107, -108, -109]) (countLit q [-111, -114, -115, -117]) (count1668 q) 1 2 (meaning1656 q) (meaning1665 q) (meaning1670 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1665 = false ∨ valuation q 1670 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1671 = true := by
  have hs : count1668 q = (countLit q [-104, -107, -108, -109]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -108, -109]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1671)) (countLit q [-104, -107, -108, -109]) (countLit q [-111, -114, -115, -117]) (count1668 q) 1 3 (meaning1656 q) (meaning1666 q) (meaning1671 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1666 = false ∨ valuation q 1671 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1670 = true := by
  have hs : count1668 q = (countLit q [-104, -107, -108, -109]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -108, -109]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1670)) (countLit q [-104, -107, -108, -109]) (countLit q [-111, -114, -115, -117]) (count1668 q) 2 1 (meaning1657 q) (meaning1664 q) (meaning1670 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1664 = false ∨ valuation q 1670 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1671 = true := by
  have hs : count1668 q = (countLit q [-104, -107, -108, -109]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -108, -109]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1671)) (countLit q [-104, -107, -108, -109]) (countLit q [-111, -114, -115, -117]) (count1668 q) 2 2 (meaning1657 q) (meaning1665 q) (meaning1671 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1665 = false ∨ valuation q 1671 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1672 = true := by
  have hs : count1668 q = (countLit q [-104, -107, -108, -109]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -108, -109]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1672)) (countLit q [-104, -107, -108, -109]) (countLit q [-111, -114, -115, -117]) (count1668 q) 2 3 (meaning1657 q) (meaning1666 q) (meaning1672 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1666 = false ∨ valuation q 1672 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1673 = true := by
  have hs : count1668 q = (countLit q [-104, -107, -108, -109]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -108, -109]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1673)) (countLit q [-104, -107, -108, -109]) (countLit q [-111, -114, -115, -117]) (count1668 q) 2 4 (meaning1657 q) (meaning1667 q) (meaning1673 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1667 = false ∨ valuation q 1673 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1671 = true := by
  have hs : count1668 q = (countLit q [-104, -107, -108, -109]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -108, -109]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1671)) (countLit q [-104, -107, -108, -109]) (countLit q [-111, -114, -115, -117]) (count1668 q) 3 1 (meaning1658 q) (meaning1664 q) (meaning1671 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1664 = false ∨ valuation q 1671 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1672 = true := by
  have hs : count1668 q = (countLit q [-104, -107, -108, -109]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -108, -109]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1672)) (countLit q [-104, -107, -108, -109]) (countLit q [-111, -114, -115, -117]) (count1668 q) 3 2 (meaning1658 q) (meaning1665 q) (meaning1672 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1665 = false ∨ valuation q 1672 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1680 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1672)) (literal (valuationOf q) (1680)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 5 (meaning1672 q) (meaning1680 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1680 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1679 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1679)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 1 3 (meaning1645 q) (meaning1670 q) (meaning1679 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1670 = false ∨ valuation q 1679 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1680 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1680)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 1 4 (meaning1645 q) (meaning1671 q) (meaning1680 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1671 = false ∨ valuation q 1680 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1681 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1681)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 1 5 (meaning1645 q) (meaning1672 q) (meaning1681 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1672 = false ∨ valuation q 1681 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1679 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1679)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 2 2 (meaning1646 q) (meaning1669 q) (meaning1679 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1669 = false ∨ valuation q 1679 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1680 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1680)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 2 3 (meaning1646 q) (meaning1670 q) (meaning1680 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1670 = false ∨ valuation q 1680 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1681 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1681)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 2 4 (meaning1646 q) (meaning1671 q) (meaning1681 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1671 = false ∨ valuation q 1681 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1682 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1682)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 2 5 (meaning1646 q) (meaning1672 q) (meaning1682 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1672 = false ∨ valuation q 1682 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1683 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1683)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 2 6 (meaning1646 q) (meaning1673 q) (meaning1683 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1673 = false ∨ valuation q 1683 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1680 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1680)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 3 2 (meaning1647 q) (meaning1669 q) (meaning1680 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1669 = false ∨ valuation q 1680 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1681 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1681)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 3 3 (meaning1647 q) (meaning1670 q) (meaning1681 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1670 = false ∨ valuation q 1681 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1682 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1682)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 3 4 (meaning1647 q) (meaning1671 q) (meaning1682 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1671 = false ∨ valuation q 1682 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1683 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1683)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 3 5 (meaning1647 q) (meaning1672 q) (meaning1683 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1672 = false ∨ valuation q 1683 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1681 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1681)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 4 2 (meaning1648 q) (meaning1669 q) (meaning1681 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1669 = false ∨ valuation q 1681 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1682 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1682)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 4 3 (meaning1648 q) (meaning1670 q) (meaning1682 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1670 = false ∨ valuation q 1682 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1683 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1683)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 4 4 (meaning1648 q) (meaning1671 q) (meaning1683 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1671 = false ∨ valuation q 1683 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1684 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1684)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 4 5 (meaning1648 q) (meaning1672 q) (meaning1684 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1672 = false ∨ valuation q 1684 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1682 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1682)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 5 2 (meaning1649 q) (meaning1669 q) (meaning1682 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1669 = false ∨ valuation q 1682 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E187.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112187
