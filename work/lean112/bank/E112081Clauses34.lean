import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1012 = true := by
  have hs : count1012 q = (countLit q [-103, -104]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-106, -109])
  have hm := merge_left (literal (valuationOf q) (1008)) (literal (valuationOf q) (1012)) (countLit q [-103, -104]) (countLit q [-106, -109]) (count1012 q) 1 (meaning1008 q) (meaning1012 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1012 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_right (literal (valuationOf q) (-111)) (literal (valuationOf q) (1016)) (countLit q [-110]) (countLit q [-111]) (count1016 q) 1 (meaningNeg111 q) (meaning1016 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1016 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1018 = true := by
  have hs : count1018 q = (countLit q [-116]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1018)) (countLit q [-116]) (countLit q [-117]) (count1018 q) 1 (meaningNeg117 q) (meaning1018 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1018 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1020 = true := by
  have hs : count1020 q = (countLit q [-110, -111]) + (countLit q [-116, -117]) := List.countP_append (p := literal q) (l₁ := [-110, -111]) (l₂ := [-116, -117])
  have hm := merge_right (literal (valuationOf q) (1018)) (literal (valuationOf q) (1020)) (countLit q [-110, -111]) (countLit q [-116, -117]) (count1020 q) 1 (meaning1018 q) (meaning1020 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1020 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1020 = true := by
  have hs : count1020 q = (countLit q [-110, -111]) + (countLit q [-116, -117]) := List.countP_append (p := literal q) (l₁ := [-110, -111]) (l₂ := [-116, -117])
  have hm := merge_left (literal (valuationOf q) (1016)) (literal (valuationOf q) (1020)) (countLit q [-110, -111]) (countLit q [-116, -117]) (count1020 q) 1 (meaning1016 q) (meaning1020 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1020 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1024 = true := by
  have hs : count1024 q = (countLit q [-103, -104, -106, -109]) + (countLit q [-110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -106, -109]) (l₂ := [-110, -111, -116, -117])
  have hm := merge_right (literal (valuationOf q) (1020)) (literal (valuationOf q) (1024)) (countLit q [-103, -104, -106, -109]) (countLit q [-110, -111, -116, -117]) (count1024 q) 1 (meaning1020 q) (meaning1024 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1024 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1024 = true := by
  have hs : count1024 q = (countLit q [-103, -104, -106, -109]) + (countLit q [-110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -106, -109]) (l₂ := [-110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (1012)) (literal (valuationOf q) (1024)) (countLit q [-103, -104, -106, -109]) (countLit q [-110, -111, -116, -117]) (count1024 q) 1 (meaning1012 q) (meaning1024 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1024 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1032 = true := by
  have hs : count1032 q = (countLit q [-87, -89, -92, -95, -96, -97, -102]) + (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92, -95, -96, -97, -102]) (l₂ := [-103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_right (literal (valuationOf q) (1024)) (literal (valuationOf q) (1032)) (countLit q [-87, -89, -92, -95, -96, -97, -102]) (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) (count1032 q) 1 (meaning1024 q) (meaning1032 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1032 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1032 = true := by
  have hs : count1032 q = (countLit q [-87, -89, -92, -95, -96, -97, -102]) + (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92, -95, -96, -97, -102]) (l₂ := [-103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (1001)) (literal (valuationOf q) (1032)) (countLit q [-87, -89, -92, -95, -96, -97, -102]) (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) (count1032 q) 1 (meaning1001 q) (meaning1032 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1032 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1033 = true := by
  have hs : count1032 q = (countLit q [-87, -89, -92, -95, -96, -97, -102]) + (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92, -95, -96, -97, -102]) (l₂ := [-103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1033)) (countLit q [-87, -89, -92, -95, -96, -97, -102]) (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) (count1032 q) 1 1 (meaning1001 q) (meaning1024 q) (meaning1033 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1024 = false ∨ valuation q 1033 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1033 = true := by
  have hs : count1032 q = (countLit q [-87, -89, -92, -95, -96, -97, -102]) + (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92, -95, -96, -97, -102]) (l₂ := [-103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (1002)) (literal (valuationOf q) (1033)) (countLit q [-87, -89, -92, -95, -96, -97, -102]) (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) (count1032 q) 2 (meaning1002 q) (meaning1033 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1033 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-87, -89, -92, -95, -96, -97, -102]) + (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92, -95, -96, -97, -102]) (l₂ := [-103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1034)) (countLit q [-87, -89, -92, -95, -96, -97, -102]) (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) (count1032 q) 2 1 (meaning1002 q) (meaning1024 q) (meaning1034 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1024 = false ∨ valuation q 1034 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-87, -89, -92, -95, -96, -97, -102]) + (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92, -95, -96, -97, -102]) (l₂ := [-103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (1003)) (literal (valuationOf q) (1034)) (countLit q [-87, -89, -92, -95, -96, -97, -102]) (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) (count1032 q) 3 (meaning1003 q) (meaning1034 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1034 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-87, -89, -92, -95, -96, -97, -102]) + (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92, -95, -96, -97, -102]) (l₂ := [-103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1035)) (countLit q [-87, -89, -92, -95, -96, -97, -102]) (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) (count1032 q) 3 1 (meaning1003 q) (meaning1024 q) (meaning1035 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1024 = false ∨ valuation q 1035 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-87, -89, -92, -95, -96, -97, -102]) + (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92, -95, -96, -97, -102]) (l₂ := [-103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (1004)) (literal (valuationOf q) (1035)) (countLit q [-87, -89, -92, -95, -96, -97, -102]) (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) (count1032 q) 4 (meaning1004 q) (meaning1035 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1035 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-87, -89, -92, -95, -96, -97, -102]) + (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92, -95, -96, -97, -102]) (l₂ := [-103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1036)) (countLit q [-87, -89, -92, -95, -96, -97, -102]) (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) (count1032 q) 4 1 (meaning1004 q) (meaning1024 q) (meaning1036 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1024 = false ∨ valuation q 1036 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-87, -89, -92, -95, -96, -97, -102]) + (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92, -95, -96, -97, -102]) (l₂ := [-103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (1005)) (literal (valuationOf q) (1036)) (countLit q [-87, -89, -92, -95, -96, -97, -102]) (countLit q [-103, -104, -106, -109, -110, -111, -116, -117]) (count1032 q) 5 (meaning1005 q) (meaning1036 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1036 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1048 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_right (literal (valuationOf q) (1033)) (literal (valuationOf q) (1048)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 2 (meaning1033 q) (meaning1048 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1048 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1048 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1051 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1051)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 1 4 (meaning973 q) (meaning1035 q) (meaning1051 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1035 = false ∨ valuation q 1051 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1049 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1049)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 2 1 (meaning974 q) (meaning1032 q) (meaning1049 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1049 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1032 = false ∨ valuation q 1049 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1050 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1050)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 2 2 (meaning974 q) (meaning1033 q) (meaning1050 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1033 = false ∨ valuation q 1050 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1051 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1051)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 2 3 (meaning974 q) (meaning1034 q) (meaning1051 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1034 = false ∨ valuation q 1051 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1052)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 2 4 (meaning974 q) (meaning1035 q) (meaning1052 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1035 = false ∨ valuation q 1052 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1050 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1050)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 3 1 (meaning975 q) (meaning1032 q) (meaning1050 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1032 = false ∨ valuation q 1050 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1051 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1051)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 3 2 (meaning975 q) (meaning1033 q) (meaning1051 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1033 = false ∨ valuation q 1051 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1052)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 3 3 (meaning975 q) (meaning1034 q) (meaning1052 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1034 = false ∨ valuation q 1052 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1053)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 3 4 (meaning975 q) (meaning1035 q) (meaning1053 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1035 = false ∨ valuation q 1053 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1054)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 3 5 (meaning975 q) (meaning1036 q) (meaning1054 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1036 = false ∨ valuation q 1054 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1050 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (976)) (literal (valuationOf q) (1050)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 4 (meaning976 q) (meaning1050 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1050 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1051 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1051)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 4 1 (meaning976 q) (meaning1032 q) (meaning1051 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1032 = false ∨ valuation q 1051 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1052)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 4 2 (meaning976 q) (meaning1033 q) (meaning1052 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1033 = false ∨ valuation q 1052 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) + (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (l₂ := [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1053)) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86]) (countLit q [-87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 4 3 (meaning976 q) (meaning1034 q) (meaning1053 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1034 = false ∨ valuation q 1053 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E081.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112081
