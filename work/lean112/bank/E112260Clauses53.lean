import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec53 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1697 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1101)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 5 2 (meaning1067 q) (meaning1088 q) (meaning1101 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1697 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1088 = false ∨ valuation q 1101 = true := counterClause1697 (baseVal q)

theorem counterClause1698 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1102)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 5 3 (meaning1067 q) (meaning1089 q) (meaning1102 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1698 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1089 = false ∨ valuation q 1102 = true := counterClause1698 (baseVal q)

theorem counterClause1699 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1103)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 5 4 (meaning1067 q) (meaning1090 q) (meaning1103 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1699 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1090 = false ∨ valuation q 1103 = true := counterClause1699 (baseVal q)

theorem counterClause1700 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1102)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 6 2 (meaning1068 q) (meaning1088 q) (meaning1102 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1700 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1088 = false ∨ valuation q 1102 = true := counterClause1700 (baseVal q)

theorem counterClause1701 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1103)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 6 3 (meaning1068 q) (meaning1089 q) (meaning1103 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1701 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1089 = false ∨ valuation q 1103 = true := counterClause1701 (baseVal q)

theorem counterClause1702 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1119)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 1 8 (meaning1032 q) (meaning1102 q) (meaning1119 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1702 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1102 = false ∨ valuation q 1119 = true := counterClause1702 (baseVal q)

theorem counterClause1703 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1117 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1117)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 2 5 (meaning1033 q) (meaning1099 q) (meaning1117 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1117 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1703 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1099 = false ∨ valuation q 1117 = true := counterClause1703 (baseVal q)

theorem counterClause1704 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1120)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 2 8 (meaning1033 q) (meaning1102 q) (meaning1120 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1704 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1102 = false ∨ valuation q 1120 = true := counterClause1704 (baseVal q)

theorem counterClause1705 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1118 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1118)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 3 5 (meaning1034 q) (meaning1099 q) (meaning1118 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1118 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1705 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1099 = false ∨ valuation q 1118 = true := counterClause1705 (baseVal q)

theorem counterClause1706 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1119)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 3 6 (meaning1034 q) (meaning1100 q) (meaning1119 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1706 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1100 = false ∨ valuation q 1119 = true := counterClause1706 (baseVal q)

theorem counterClause1707 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1120)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 3 7 (meaning1034 q) (meaning1101 q) (meaning1120 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1707 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1101 = false ∨ valuation q 1120 = true := counterClause1707 (baseVal q)

theorem counterClause1708 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1121)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 3 8 (meaning1034 q) (meaning1102 q) (meaning1121 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1708 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1102 = false ∨ valuation q 1121 = true := counterClause1708 (baseVal q)

theorem counterClause1709 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1103)) (literal (valuationOf q) (1122)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 3 9 (meaning1034 q) (meaning1103 q) (meaning1122 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1709 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1103 = false ∨ valuation q 1122 = true := counterClause1709 (baseVal q)

theorem counterClause1710 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1118 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1118)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 4 4 (meaning1035 q) (meaning1098 q) (meaning1118 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1118 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1710 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1098 = false ∨ valuation q 1118 = true := counterClause1710 (baseVal q)

theorem counterClause1711 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1119)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 4 5 (meaning1035 q) (meaning1099 q) (meaning1119 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1711 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1099 = false ∨ valuation q 1119 = true := counterClause1711 (baseVal q)

theorem counterClause1712 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1120)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 4 6 (meaning1035 q) (meaning1100 q) (meaning1120 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1712 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1100 = false ∨ valuation q 1120 = true := counterClause1712 (baseVal q)

theorem counterClause1713 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1121)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 4 7 (meaning1035 q) (meaning1101 q) (meaning1121 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1713 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1101 = false ∨ valuation q 1121 = true := counterClause1713 (baseVal q)

theorem counterClause1714 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1122)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 4 8 (meaning1035 q) (meaning1102 q) (meaning1122 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1714 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1102 = false ∨ valuation q 1122 = true := counterClause1714 (baseVal q)

theorem counterClause1715 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1103)) (literal (valuationOf q) (1123)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 4 9 (meaning1035 q) (meaning1103 q) (meaning1123 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1715 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1103 = false ∨ valuation q 1123 = true := counterClause1715 (baseVal q)

theorem counterClause1716 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1118 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1118)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 5 3 (meaning1036 q) (meaning1097 q) (meaning1118 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1118 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1716 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1097 = false ∨ valuation q 1118 = true := counterClause1716 (baseVal q)

theorem counterClause1717 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1119)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 5 4 (meaning1036 q) (meaning1098 q) (meaning1119 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1717 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1098 = false ∨ valuation q 1119 = true := counterClause1717 (baseVal q)

theorem counterClause1718 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1120)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 5 5 (meaning1036 q) (meaning1099 q) (meaning1120 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1718 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1099 = false ∨ valuation q 1120 = true := counterClause1718 (baseVal q)

theorem counterClause1719 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1121)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 5 6 (meaning1036 q) (meaning1100 q) (meaning1121 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1719 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1100 = false ∨ valuation q 1121 = true := counterClause1719 (baseVal q)

theorem counterClause1720 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1122)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 5 7 (meaning1036 q) (meaning1101 q) (meaning1122 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1720 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1101 = false ∨ valuation q 1122 = true := counterClause1720 (baseVal q)

theorem counterClause1721 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1123)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 5 8 (meaning1036 q) (meaning1102 q) (meaning1123 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1721 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1102 = false ∨ valuation q 1123 = true := counterClause1721 (baseVal q)

theorem counterClause1722 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1119)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 6 3 (meaning1037 q) (meaning1097 q) (meaning1119 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1722 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1097 = false ∨ valuation q 1119 = true := counterClause1722 (baseVal q)

theorem counterClause1723 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1120)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 6 4 (meaning1037 q) (meaning1098 q) (meaning1120 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1723 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1098 = false ∨ valuation q 1120 = true := counterClause1723 (baseVal q)

theorem counterClause1724 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1121)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 6 5 (meaning1037 q) (meaning1099 q) (meaning1121 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1724 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1099 = false ∨ valuation q 1121 = true := counterClause1724 (baseVal q)

theorem counterClause1725 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1122)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 6 6 (meaning1037 q) (meaning1100 q) (meaning1122 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1725 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1100 = false ∨ valuation q 1122 = true := counterClause1725 (baseVal q)

theorem counterClause1726 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1123)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 6 7 (meaning1037 q) (meaning1101 q) (meaning1123 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1726 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1101 = false ∨ valuation q 1123 = true := counterClause1726 (baseVal q)

theorem counterClause1727 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1124)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 6 8 (meaning1037 q) (meaning1102 q) (meaning1124 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1727 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1102 = false ∨ valuation q 1124 = true := counterClause1727 (baseVal q)

theorem counterClause1728 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1120)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 7 3 (meaning1038 q) (meaning1097 q) (meaning1120 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1728 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1097 = false ∨ valuation q 1120 = true := counterClause1728 (baseVal q)

theorem block53 (q : Snake 81) (h : Conditions q) : B112E260.Block53 (valuation q) :=
  ⟨clause1697 q h, clause1698 q h, clause1699 q h, clause1700 q h, clause1701 q h, clause1702 q h, clause1703 q h, clause1704 q h, clause1705 q h, clause1706 q h, clause1707 q h, clause1708 q h, clause1709 q h, clause1710 q h, clause1711 q h, clause1712 q h, clause1713 q h, clause1714 q h, clause1715 q h, clause1716 q h, clause1717 q h, clause1718 q h, clause1719 q h, clause1720 q h, clause1721 q h, clause1722 q h, clause1723 q h, clause1724 q h, clause1725 q h, clause1726 q h, clause1727 q h, clause1728 q h⟩

end
end Snake9.Regrowth.E112260
