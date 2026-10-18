import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-91, -93, -94, -97, -99, -100, -101]) + (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -97, -99, -100, -101]) (l₂ := [-103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1036)) (countLit q [-91, -93, -94, -97, -99, -100, -101]) (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) (count1032 q) 4 1 (meaning1004 q) (meaning1024 q) (meaning1036 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1024 = false ∨ valuation q 1036 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-91, -93, -94, -97, -99, -100, -101]) + (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -97, -99, -100, -101]) (l₂ := [-103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1038)) (countLit q [-91, -93, -94, -97, -99, -100, -101]) (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) (count1032 q) 4 3 (meaning1004 q) (meaning1026 q) (meaning1038 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1026 = false ∨ valuation q 1038 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-91, -93, -94, -97, -99, -100, -101]) + (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -97, -99, -100, -101]) (l₂ := [-103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1037)) (countLit q [-91, -93, -94, -97, -99, -100, -101]) (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) (count1032 q) 5 1 (meaning1005 q) (meaning1024 q) (meaning1037 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1024 = false ∨ valuation q 1037 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-91, -93, -94, -97, -99, -100, -101]) + (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -97, -99, -100, -101]) (l₂ := [-103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1038)) (countLit q [-91, -93, -94, -97, -99, -100, -101]) (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) (count1032 q) 5 2 (meaning1005 q) (meaning1025 q) (meaning1038 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1025 = false ∨ valuation q 1038 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-91, -93, -94, -97, -99, -100, -101]) + (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -97, -99, -100, -101]) (l₂ := [-103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1038)) (countLit q [-91, -93, -94, -97, -99, -100, -101]) (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) (count1032 q) 6 1 (meaning1006 q) (meaning1024 q) (meaning1038 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1024 = false ∨ valuation q 1038 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1040 = true := by
  have hs : count1032 q = (countLit q [-91, -93, -94, -97, -99, -100, -101]) + (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -97, -99, -100, -101]) (l₂ := [-103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1040)) (countLit q [-91, -93, -94, -97, -99, -100, -101]) (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) (count1032 q) 6 3 (meaning1006 q) (meaning1026 q) (meaning1040 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1026 = false ∨ valuation q 1040 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1050 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_right (literal (valuationOf q) (1035)) (literal (valuationOf q) (1050)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 4 (meaning1035 q) (meaning1050 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1050 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1051 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_right (literal (valuationOf q) (1036)) (literal (valuationOf q) (1051)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 5 (meaning1036 q) (meaning1051 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1051 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_right (literal (valuationOf q) (1037)) (literal (valuationOf q) (1052)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 6 (meaning1037 q) (meaning1052 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1052 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1050 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1050)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 1 3 (meaning973 q) (meaning1034 q) (meaning1050 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1034 = false ∨ valuation q 1050 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1051 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1051)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 1 4 (meaning973 q) (meaning1035 q) (meaning1051 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1035 = false ∨ valuation q 1051 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1052)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 1 5 (meaning973 q) (meaning1036 q) (meaning1052 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1036 = false ∨ valuation q 1052 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1053)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 1 6 (meaning973 q) (meaning1037 q) (meaning1053 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1037 = false ∨ valuation q 1053 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1054)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 1 7 (meaning973 q) (meaning1038 q) (meaning1054 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1038 = false ∨ valuation q 1054 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1051 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1051)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 2 3 (meaning974 q) (meaning1034 q) (meaning1051 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1034 = false ∨ valuation q 1051 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1052)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 2 4 (meaning974 q) (meaning1035 q) (meaning1052 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1035 = false ∨ valuation q 1052 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1053)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 2 5 (meaning974 q) (meaning1036 q) (meaning1053 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1036 = false ∨ valuation q 1053 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1054)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 2 6 (meaning974 q) (meaning1037 q) (meaning1054 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1037 = false ∨ valuation q 1054 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1055)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 2 7 (meaning974 q) (meaning1038 q) (meaning1055 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1038 = false ∨ valuation q 1055 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1057 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1040)) (literal (valuationOf q) (1057)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 2 9 (meaning974 q) (meaning1040 q) (meaning1057 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1040 = false ∨ valuation q 1057 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1052)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 3 3 (meaning975 q) (meaning1034 q) (meaning1052 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1034 = false ∨ valuation q 1052 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1053)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 3 4 (meaning975 q) (meaning1035 q) (meaning1053 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1035 = false ∨ valuation q 1053 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1054)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 3 5 (meaning975 q) (meaning1036 q) (meaning1054 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1036 = false ∨ valuation q 1054 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1055)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 3 6 (meaning975 q) (meaning1037 q) (meaning1055 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1037 = false ∨ valuation q 1055 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1056)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 3 7 (meaning975 q) (meaning1038 q) (meaning1056 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1038 = false ∨ valuation q 1056 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1053)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 4 3 (meaning976 q) (meaning1034 q) (meaning1053 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1034 = false ∨ valuation q 1053 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1054)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 4 4 (meaning976 q) (meaning1035 q) (meaning1054 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1035 = false ∨ valuation q 1054 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1055)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 4 5 (meaning976 q) (meaning1036 q) (meaning1055 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1036 = false ∨ valuation q 1055 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1056)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 4 6 (meaning976 q) (meaning1037 q) (meaning1056 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1037 = false ∨ valuation q 1056 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1057 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1057)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 4 7 (meaning976 q) (meaning1038 q) (meaning1057 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1038 = false ∨ valuation q 1057 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1054)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 5 3 (meaning977 q) (meaning1034 q) (meaning1054 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1034 = false ∨ valuation q 1054 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1055)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 5 4 (meaning977 q) (meaning1035 q) (meaning1055 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1035 = false ∨ valuation q 1055 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E213.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112213
