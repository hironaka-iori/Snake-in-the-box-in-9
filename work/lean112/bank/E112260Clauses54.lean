import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec54 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1729 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1121)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 7 4 (meaning1038 q) (meaning1098 q) (meaning1121 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1729 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1098 = false ∨ valuation q 1121 = true := counterClause1729 (baseVal q)

theorem counterClause1730 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1122)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 7 5 (meaning1038 q) (meaning1099 q) (meaning1122 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1730 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1099 = false ∨ valuation q 1122 = true := counterClause1730 (baseVal q)

theorem counterClause1731 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1123)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 7 6 (meaning1038 q) (meaning1100 q) (meaning1123 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1731 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1100 = false ∨ valuation q 1123 = true := counterClause1731 (baseVal q)

theorem counterClause1732 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1124)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 7 7 (meaning1038 q) (meaning1101 q) (meaning1124 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1732 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1101 = false ∨ valuation q 1124 = true := counterClause1732 (baseVal q)

theorem counterClause1733 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1125 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1125)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 7 8 (meaning1038 q) (meaning1102 q) (meaning1125 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1125 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1733 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1102 = false ∨ valuation q 1125 = true := counterClause1733 (baseVal q)

theorem counterClause1734 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1121)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 8 3 (meaning1039 q) (meaning1097 q) (meaning1121 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1734 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1097 = false ∨ valuation q 1121 = true := counterClause1734 (baseVal q)

theorem counterClause1735 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1122)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 8 4 (meaning1039 q) (meaning1098 q) (meaning1122 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1735 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1098 = false ∨ valuation q 1122 = true := counterClause1735 (baseVal q)

theorem counterClause1736 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1123)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 8 5 (meaning1039 q) (meaning1099 q) (meaning1123 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1736 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1099 = false ∨ valuation q 1123 = true := counterClause1736 (baseVal q)

theorem counterClause1737 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1124)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 8 6 (meaning1039 q) (meaning1100 q) (meaning1124 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1737 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1100 = false ∨ valuation q 1124 = true := counterClause1737 (baseVal q)

theorem counterClause1738 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1122)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 9 3 (meaning1040 q) (meaning1097 q) (meaning1122 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1738 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1097 = false ∨ valuation q 1122 = true := counterClause1738 (baseVal q)

theorem counterClause1739 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1123)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 9 4 (meaning1040 q) (meaning1098 q) (meaning1123 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1739 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1098 = false ∨ valuation q 1123 = true := counterClause1739 (baseVal q)

theorem counterClause1740 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1124)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 9 5 (meaning1040 q) (meaning1099 q) (meaning1124 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1740 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1099 = false ∨ valuation q 1124 = true := counterClause1740 (baseVal q)

theorem counterClause1741 (q : Nat → Bool) : valuationOf q 1041 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1041)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1123)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 10 3 (meaning1041 q) (meaning1097 q) (meaning1123 q) hs
  change valuationOf q 1041 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1741 (q : Snake 81) (h : Conditions q) : valuation q 1041 = false ∨ valuation q 1097 = false ∨ valuation q 1123 = true := counterClause1741 (baseVal q)

theorem counterClause1742 (q : Nat → Bool) : valuationOf q 1041 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1125 = true := by
  have hs : count1111 q = (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) + (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (l₂ := [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1041)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1125)) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90]) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1111 q) 10 5 (meaning1041 q) (meaning1099 q) (meaning1125 q) hs
  change valuationOf q 1041 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1125 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1742 (q : Snake 81) (h : Conditions q) : valuation q 1041 = false ∨ valuation q 1099 = false ∨ valuation q 1125 = true := counterClause1742 (baseVal q)

theorem counterClause1743 (q : Nat → Bool) : valuationOf q 972 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) + (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (l₂ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (972)) (literal (valuationOf q) (1125)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1132 q) 6 15 (meaning972 q) (meaning1125 q) (meaning1152 q) hs
  change valuationOf q 972 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1743 (q : Snake 81) (h : Conditions q) : valuation q 972 = false ∨ valuation q 1125 = false ∨ valuation q 1152 = true := counterClause1743 (baseVal q)

theorem counterClause1744 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) + (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (l₂ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1124)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1132 q) 7 14 (meaning973 q) (meaning1124 q) (meaning1152 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1744 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1124 = false ∨ valuation q 1152 = true := counterClause1744 (baseVal q)

theorem counterClause1745 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) + (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (l₂ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1123)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1132 q) 8 13 (meaning974 q) (meaning1123 q) (meaning1152 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1745 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1123 = false ∨ valuation q 1152 = true := counterClause1745 (baseVal q)

theorem counterClause1746 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1122 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) + (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (l₂ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1122)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1132 q) 9 12 (meaning975 q) (meaning1122 q) (meaning1152 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1122 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1746 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1122 = false ∨ valuation q 1152 = true := counterClause1746 (baseVal q)

theorem counterClause1747 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) + (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (l₂ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1121)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1132 q) 10 11 (meaning976 q) (meaning1121 q) (meaning1152 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1747 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1121 = false ∨ valuation q 1152 = true := counterClause1747 (baseVal q)

theorem counterClause1748 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) + (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (l₂ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1120)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1132 q) 11 10 (meaning977 q) (meaning1120 q) (meaning1152 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1748 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1120 = false ∨ valuation q 1152 = true := counterClause1748 (baseVal q)

theorem counterClause1749 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) + (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (l₂ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1119)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1132 q) 12 9 (meaning978 q) (meaning1119 q) (meaning1152 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1749 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1119 = false ∨ valuation q 1152 = true := counterClause1749 (baseVal q)

theorem counterClause1750 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1118 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) + (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (l₂ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1118)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1132 q) 13 8 (meaning979 q) (meaning1118 q) (meaning1152 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1118 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1750 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1118 = false ∨ valuation q 1152 = true := counterClause1750 (baseVal q)

theorem counterClause1751 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1117 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) + (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (l₂ := [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1117)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30, -32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (countLit q [-65, -67, -68, -69, -72, -73, -74, -76, -79, -81, -82, -85, -86, -89, -90, -96, -98, -100, -103, -105, -108, -110, -111, -113, -115, -117, -119, -122, -124, -126, -127]) (count1132 q) 14 7 (meaning980 q) (meaning1117 q) (meaning1152 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1117 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1751 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1117 = false ∨ valuation q 1152 = true := counterClause1751 (baseVal q)

theorem clause1752 (q : Snake 81) (h : Conditions q) : valuation q 1152 = false := by
  rw [value1152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1132 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause1753 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_right (literal (valuationOf q) (-4)) (literal (valuationOf q) (1529)) (countLit q [-3]) (countLit q [-4]) (count1529 q) 1 (meaningNeg4 q) (meaning1529 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1753 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1529 = true := counterClause1753 (baseVal q)

theorem counterClause1754 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1529)) (countLit q [-3]) (countLit q [-4]) (count1529 q) 1 (meaningNeg3 q) (meaning1529 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1754 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1529 = true := counterClause1754 (baseVal q)

theorem counterClause1755 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 4 = true ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-4)) (literal (valuationOf q) (1530)) (countLit q [-3]) (countLit q [-4]) (count1529 q) 1 1 (meaningNeg3 q) (meaningNeg4 q) (meaning1530 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 4)) = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1755 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 4 = true ∨ valuation q 1530 = true := counterClause1755 (baseVal q)

theorem counterClause1756 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_right (literal (valuationOf q) (-9)) (literal (valuationOf q) (1531)) (countLit q [-8]) (countLit q [-9]) (count1531 q) 1 (meaningNeg9 q) (meaning1531 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1756 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1531 = true := counterClause1756 (baseVal q)

theorem counterClause1757 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1531)) (countLit q [-8]) (countLit q [-9]) (count1531 q) 1 (meaningNeg8 q) (meaning1531 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1757 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1531 = true := counterClause1757 (baseVal q)

theorem counterClause1758 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 9 = true ∨ valuationOf q 1532 = true := by
  have hs : count1531 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-9)) (literal (valuationOf q) (1532)) (countLit q [-8]) (countLit q [-9]) (count1531 q) 1 1 (meaningNeg8 q) (meaningNeg9 q) (meaning1532 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 9)) = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1758 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 9 = true ∨ valuation q 1532 = true := counterClause1758 (baseVal q)

theorem counterClause1759 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-3, -4]) + (countLit q [-8, -9]) := List.countP_append (p := literal q) (l₁ := [-3, -4]) (l₂ := [-8, -9])
  have hm := merge_right (literal (valuationOf q) (1531)) (literal (valuationOf q) (1533)) (countLit q [-3, -4]) (countLit q [-8, -9]) (count1533 q) 1 (meaning1531 q) (meaning1533 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1759 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1533 = true := counterClause1759 (baseVal q)

theorem counterClause1760 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-3, -4]) + (countLit q [-8, -9]) := List.countP_append (p := literal q) (l₁ := [-3, -4]) (l₂ := [-8, -9])
  have hm := merge_right (literal (valuationOf q) (1532)) (literal (valuationOf q) (1534)) (countLit q [-3, -4]) (countLit q [-8, -9]) (count1533 q) 2 (meaning1532 q) (meaning1534 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1760 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1534 = true := counterClause1760 (baseVal q)

theorem block54 (q : Snake 81) (h : Conditions q) : B112E260.Block54 (valuation q) :=
  ⟨clause1729 q h, clause1730 q h, clause1731 q h, clause1732 q h, clause1733 q h, clause1734 q h, clause1735 q h, clause1736 q h, clause1737 q h, clause1738 q h, clause1739 q h, clause1740 q h, clause1741 q h, clause1742 q h, clause1743 q h, clause1744 q h, clause1745 q h, clause1746 q h, clause1747 q h, clause1748 q h, clause1749 q h, clause1750 q h, clause1751 q h, clause1752 q h, clause1753 q h, clause1754 q h, clause1755 q h, clause1756 q h, clause1757 q h, clause1758 q h, clause1759 q h, clause1760 q h⟩

end
end Snake9.Regrowth.E112260
