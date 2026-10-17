import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1669 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_left (literal (valuationOf q) (1657)) (literal (valuationOf q) (1669)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 2 (meaning1657 q) (meaning1669 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1669 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1670 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1670)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 2 1 (meaning1657 q) (meaning1664 q) (meaning1670 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1664 = false ∨ valuation q 1670 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1671 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1671)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 2 2 (meaning1657 q) (meaning1665 q) (meaning1671 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1665 = false ∨ valuation q 1671 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1670 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_left (literal (valuationOf q) (1658)) (literal (valuationOf q) (1670)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 3 (meaning1658 q) (meaning1670 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1670 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1671 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1671)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 3 1 (meaning1658 q) (meaning1664 q) (meaning1671 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1664 = false ∨ valuation q 1671 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1672 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1672)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 3 2 (meaning1658 q) (meaning1665 q) (meaning1672 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1665 = false ∨ valuation q 1672 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1672 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1672)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 4 1 (meaning1659 q) (meaning1664 q) (meaning1672 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1664 = false ∨ valuation q 1672 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1679 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_right (literal (valuationOf q) (1671)) (literal (valuationOf q) (1679)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 4 (meaning1671 q) (meaning1679 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1679 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1677 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1677)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 1 1 (meaning1645 q) (meaning1668 q) (meaning1677 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1668 = false ∨ valuation q 1677 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1678 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1678)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 1 2 (meaning1645 q) (meaning1669 q) (meaning1678 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1669 = false ∨ valuation q 1678 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1679 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1679)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 1 3 (meaning1645 q) (meaning1670 q) (meaning1679 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1670 = false ∨ valuation q 1679 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1680 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1680)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 1 4 (meaning1645 q) (meaning1671 q) (meaning1680 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1671 = false ∨ valuation q 1680 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1681 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1681)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 1 5 (meaning1645 q) (meaning1672 q) (meaning1681 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1672 = false ∨ valuation q 1681 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1678 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1678)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 2 1 (meaning1646 q) (meaning1668 q) (meaning1678 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1668 = false ∨ valuation q 1678 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1679 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1679)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 2 2 (meaning1646 q) (meaning1669 q) (meaning1679 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1669 = false ∨ valuation q 1679 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1680 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1680)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 2 3 (meaning1646 q) (meaning1670 q) (meaning1680 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1670 = false ∨ valuation q 1680 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1681 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1681)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 2 4 (meaning1646 q) (meaning1671 q) (meaning1681 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1671 = false ∨ valuation q 1681 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1679 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1679)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 3 1 (meaning1647 q) (meaning1668 q) (meaning1679 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1668 = false ∨ valuation q 1679 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1680 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1680)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 3 2 (meaning1647 q) (meaning1669 q) (meaning1680 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1669 = false ∨ valuation q 1680 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1681 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1681)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 3 3 (meaning1647 q) (meaning1670 q) (meaning1681 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1670 = false ∨ valuation q 1681 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1682 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1682)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 3 4 (meaning1647 q) (meaning1671 q) (meaning1682 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1671 = false ∨ valuation q 1682 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1679 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_left (literal (valuationOf q) (1648)) (literal (valuationOf q) (1679)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 4 (meaning1648 q) (meaning1679 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1679 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1680 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1680)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 4 1 (meaning1648 q) (meaning1668 q) (meaning1680 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1668 = false ∨ valuation q 1680 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1681 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1681)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 4 2 (meaning1648 q) (meaning1669 q) (meaning1681 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1669 = false ∨ valuation q 1681 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1682 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -96, -97, -98, -99, -103]) + (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96, -97, -98, -99, -103]) (l₂ := [-105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1682)) (countLit q [-90, -92, -96, -97, -98, -99, -103]) (countLit q [-105, -106, -107, -109, -112, -115, -116, -118]) (count1676 q) 4 3 (meaning1648 q) (meaning1670 q) (meaning1682 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1670 = false ∨ valuation q 1682 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1695 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1695)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 1 4 (meaning1618 q) (meaning1679 q) (meaning1695 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1679 = false ∨ valuation q 1695 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1696)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 1 5 (meaning1618 q) (meaning1680 q) (meaning1696 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1680 = false ∨ valuation q 1696 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1697)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 1 6 (meaning1618 q) (meaning1681 q) (meaning1697 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1681 = false ∨ valuation q 1697 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1694 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1694)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 2 2 (meaning1619 q) (meaning1677 q) (meaning1694 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1677 = false ∨ valuation q 1694 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1695 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1695)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 2 3 (meaning1619 q) (meaning1678 q) (meaning1695 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1678 = false ∨ valuation q 1695 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1696)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 2 4 (meaning1619 q) (meaning1679 q) (meaning1696 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1679 = false ∨ valuation q 1696 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1697)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 2 5 (meaning1619 q) (meaning1680 q) (meaning1697 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1680 = false ∨ valuation q 1697 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E078.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112078
