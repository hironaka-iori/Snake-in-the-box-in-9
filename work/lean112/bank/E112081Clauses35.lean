import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1054)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 4 4 (meaning976 q) (meaning1035 q) (meaning1054 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1035 = false ∨ valuation q 1054 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1051 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (977)) (literal (valuationOf q) (1051)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 5 (meaning977 q) (meaning1051 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1051 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1052)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 5 1 (meaning977 q) (meaning1032 q) (meaning1052 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1032 = false ∨ valuation q 1052 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1053)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 5 2 (meaning977 q) (meaning1033 q) (meaning1053 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1033 = false ∨ valuation q 1053 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1054)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 5 3 (meaning977 q) (meaning1034 q) (meaning1054 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1034 = false ∨ valuation q 1054 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1055)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 5 4 (meaning977 q) (meaning1035 q) (meaning1055 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1035 = false ∨ valuation q 1055 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (978)) (literal (valuationOf q) (1052)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 6 (meaning978 q) (meaning1052 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1052 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1053)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 6 1 (meaning978 q) (meaning1032 q) (meaning1053 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1032 = false ∨ valuation q 1053 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1054)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 6 2 (meaning978 q) (meaning1033 q) (meaning1054 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1033 = false ∨ valuation q 1054 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1055)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 6 3 (meaning978 q) (meaning1034 q) (meaning1055 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1034 = false ∨ valuation q 1055 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1056)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 6 4 (meaning978 q) (meaning1035 q) (meaning1056 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1035 = false ∨ valuation q 1056 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (979)) (literal (valuationOf q) (1053)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 7 (meaning979 q) (meaning1053 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1053 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1054)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 7 1 (meaning979 q) (meaning1032 q) (meaning1054 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1032 = false ∨ valuation q 1054 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1055)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 7 2 (meaning979 q) (meaning1033 q) (meaning1055 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1033 = false ∨ valuation q 1055 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1056)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 7 3 (meaning979 q) (meaning1034 q) (meaning1056 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1034 = false ∨ valuation q 1056 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (980)) (literal (valuationOf q) (1054)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 8 (meaning980 q) (meaning1054 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1054 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1055)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 8 1 (meaning980 q) (meaning1032 q) (meaning1055 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1032 = false ∨ valuation q 1055 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1056)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 8 2 (meaning980 q) (meaning1033 q) (meaning1056 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1033 = false ∨ valuation q 1056 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1057 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1057)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 8 3 (meaning980 q) (meaning1034 q) (meaning1057 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1034 = false ∨ valuation q 1057 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (981)) (literal (valuationOf q) (1055)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 9 (meaning981 q) (meaning1055 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 1055 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (981)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1056)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 9 1 (meaning981 q) (meaning1032 q) (meaning1056 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 1032 = false ∨ valuation q 1056 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1057 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (981)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1057)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 9 2 (meaning981 q) (meaning1033 q) (meaning1057 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 1033 = false ∨ valuation q 1057 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1058 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (981)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1058)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 9 3 (meaning981 q) (meaning1034 q) (meaning1058 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 1034 = false ∨ valuation q 1058 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 982 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1058 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (982)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1058)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 10 2 (meaning982 q) (meaning1033 q) (meaning1058 q) hs
  change valuationOf q 982 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 982 = false ∨ valuation q 1033 = false ∨ valuation q 1058 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) + (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (l₂ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 7 12 (meaning916 q) (meaning1058 q) (meaning1084 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 1058 = false ∨ valuation q 1084 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) + (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (l₂ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 8 11 (meaning917 q) (meaning1057 q) (meaning1084 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 1057 = false ∨ valuation q 1084 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) + (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (l₂ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 9 10 (meaning918 q) (meaning1056 q) (meaning1084 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 1056 = false ∨ valuation q 1084 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) + (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (l₂ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (1055)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 10 9 (meaning919 q) (meaning1055 q) (meaning1084 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 1055 = false ∨ valuation q 1084 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) + (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (l₂ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (1054)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 11 8 (meaning920 q) (meaning1054 q) (meaning1084 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 1054 = false ∨ valuation q 1084 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) + (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (l₂ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (1053)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 12 7 (meaning921 q) (meaning1053 q) (meaning1084 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 1053 = false ∨ valuation q 1084 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) + (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (l₂ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (1052)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 13 6 (meaning922 q) (meaning1052 q) (meaning1084 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 1052 = false ∨ valuation q 1084 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) + (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (l₂ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (1051)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 14 5 (meaning923 q) (meaning1051 q) (meaning1084 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 1051 = false ∨ valuation q 1084 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E081.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112081
