import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1680 = true := by
  have hs : count1679 q = (countLit q [-84, -87]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -87]) (l₂ := [-91, -92])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1680)) (countLit q [-84, -87]) (countLit q [-91, -92]) (count1679 q) 1 1 (meaning1675 q) (meaning1677 q) (meaning1680 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1677 = false ∨ valuation q 1680 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1681 = true := by
  have hs : count1679 q = (countLit q [-84, -87]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -87]) (l₂ := [-91, -92])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1681)) (countLit q [-84, -87]) (countLit q [-91, -92]) (count1679 q) 1 2 (meaning1675 q) (meaning1678 q) (meaning1681 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1678 = false ∨ valuation q 1681 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1680 = true := by
  have hs : count1679 q = (countLit q [-84, -87]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -87]) (l₂ := [-91, -92])
  have hm := merge_left (literal (valuationOf q) (1676)) (literal (valuationOf q) (1680)) (countLit q [-84, -87]) (countLit q [-91, -92]) (count1679 q) 2 (meaning1676 q) (meaning1680 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1680 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1681 = true := by
  have hs : count1679 q = (countLit q [-84, -87]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -87]) (l₂ := [-91, -92])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1681)) (countLit q [-84, -87]) (countLit q [-91, -92]) (count1679 q) 2 1 (meaning1676 q) (meaning1677 q) (meaning1681 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1677 = false ∨ valuation q 1681 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1682 = true := by
  have hs : count1679 q = (countLit q [-84, -87]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -87]) (l₂ := [-91, -92])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1682)) (countLit q [-84, -87]) (countLit q [-91, -92]) (count1679 q) 2 2 (meaning1676 q) (meaning1678 q) (meaning1682 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1678 = false ∨ valuation q 1682 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1683 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_left (literal (valuationOf q) (1671)) (literal (valuationOf q) (1683)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 1 (meaning1671 q) (meaning1683 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1683 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1684 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1684)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 1 1 (meaning1671 q) (meaning1679 q) (meaning1684 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1679 = false ∨ valuation q 1684 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1685 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1685)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 1 2 (meaning1671 q) (meaning1680 q) (meaning1685 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1680 = false ∨ valuation q 1685 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1686 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1686)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 1 3 (meaning1671 q) (meaning1681 q) (meaning1686 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1681 = false ∨ valuation q 1686 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1687 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1687)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 1 4 (meaning1671 q) (meaning1682 q) (meaning1687 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1682 = false ∨ valuation q 1687 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1684 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_left (literal (valuationOf q) (1672)) (literal (valuationOf q) (1684)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 2 (meaning1672 q) (meaning1684 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1684 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1685 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1685)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 2 1 (meaning1672 q) (meaning1679 q) (meaning1685 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1679 = false ∨ valuation q 1685 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1686 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1686)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 2 2 (meaning1672 q) (meaning1680 q) (meaning1686 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1680 = false ∨ valuation q 1686 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1687 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1687)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 2 3 (meaning1672 q) (meaning1681 q) (meaning1687 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1681 = false ∨ valuation q 1687 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1688 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1688)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 2 4 (meaning1672 q) (meaning1682 q) (meaning1688 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1682 = false ∨ valuation q 1688 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1685 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_left (literal (valuationOf q) (1673)) (literal (valuationOf q) (1685)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 3 (meaning1673 q) (meaning1685 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1685 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1686 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1686)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 3 1 (meaning1673 q) (meaning1679 q) (meaning1686 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1679 = false ∨ valuation q 1686 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1687 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1687)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 3 2 (meaning1673 q) (meaning1680 q) (meaning1687 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1680 = false ∨ valuation q 1687 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1688 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1688)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 3 3 (meaning1673 q) (meaning1681 q) (meaning1688 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1681 = false ∨ valuation q 1688 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1689 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1689)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 3 4 (meaning1673 q) (meaning1682 q) (meaning1689 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1682 = false ∨ valuation q 1689 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1686 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_left (literal (valuationOf q) (1674)) (literal (valuationOf q) (1686)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 4 (meaning1674 q) (meaning1686 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1686 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1687 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1687)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 4 1 (meaning1674 q) (meaning1679 q) (meaning1687 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1679 = false ∨ valuation q 1687 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1688 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1688)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 4 2 (meaning1674 q) (meaning1680 q) (meaning1688 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1680 = false ∨ valuation q 1688 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1689 = true := by
  have hs : count1683 q = (countLit q [-76, -78, -81, -83]) + (countLit q [-84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -81, -83]) (l₂ := [-84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1689)) (countLit q [-76, -78, -81, -83]) (countLit q [-84, -87, -91, -92]) (count1683 q) 4 3 (meaning1674 q) (meaning1681 q) (meaning1689 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1681 = false ∨ valuation q 1689 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1691 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_right (literal (valuationOf q) (1683)) (literal (valuationOf q) (1691)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 1 (meaning1683 q) (meaning1691 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1691 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 1684 = false ∨ valuationOf q 1692 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_right (literal (valuationOf q) (1684)) (literal (valuationOf q) (1692)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 2 (meaning1684 q) (meaning1692 q) hs
  change valuationOf q 1684 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 1684 = false ∨ valuation q 1692 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 1685 = false ∨ valuationOf q 1693 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_right (literal (valuationOf q) (1685)) (literal (valuationOf q) (1693)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 3 (meaning1685 q) (meaning1693 q) hs
  change valuationOf q 1685 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 1685 = false ∨ valuation q 1693 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1686 = false ∨ valuationOf q 1694 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_right (literal (valuationOf q) (1686)) (literal (valuationOf q) (1694)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 4 (meaning1686 q) (meaning1694 q) hs
  change valuationOf q 1686 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1686 = false ∨ valuation q 1694 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1687 = false ∨ valuationOf q 1695 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_right (literal (valuationOf q) (1687)) (literal (valuationOf q) (1695)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 5 (meaning1687 q) (meaning1695 q) hs
  change valuationOf q 1687 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1695 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_right (literal (valuationOf q) (1688)) (literal (valuationOf q) (1696)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 6 (meaning1688 q) (meaning1696 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1696 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_right (literal (valuationOf q) (1689)) (literal (valuationOf q) (1697)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 7 (meaning1689 q) (meaning1697 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1697 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1693 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1693)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 1 2 (meaning1659 q) (meaning1684 q) (meaning1693 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1684 = false ∨ valuation q 1693 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E186.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112186
