import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) + (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (l₂ := [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1055)) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 6 3 (meaning978 q) (meaning1034 q) (meaning1055 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1034 = false ∨ valuation q 1055 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) + (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (l₂ := [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1056)) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 6 4 (meaning978 q) (meaning1035 q) (meaning1056 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1035 = false ∨ valuation q 1056 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) + (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (l₂ := [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (979)) (literal (valuationOf q) (1053)) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 7 (meaning979 q) (meaning1053 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1053 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) + (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (l₂ := [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1054)) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 7 1 (meaning979 q) (meaning1032 q) (meaning1054 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1032 = false ∨ valuation q 1054 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) + (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (l₂ := [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1055)) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 7 2 (meaning979 q) (meaning1033 q) (meaning1055 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1033 = false ∨ valuation q 1055 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) + (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (l₂ := [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1056)) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 7 3 (meaning979 q) (meaning1034 q) (meaning1056 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1034 = false ∨ valuation q 1056 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) + (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (l₂ := [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (980)) (literal (valuationOf q) (1054)) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 8 (meaning980 q) (meaning1054 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1054 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) + (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (l₂ := [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1055)) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 8 1 (meaning980 q) (meaning1032 q) (meaning1055 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1032 = false ∨ valuation q 1055 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) + (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (l₂ := [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1056)) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 8 2 (meaning980 q) (meaning1033 q) (meaning1056 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1033 = false ∨ valuation q 1056 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1057 = true := by
  have hs : count1047 q = (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) + (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (l₂ := [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1057)) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 8 3 (meaning980 q) (meaning1034 q) (meaning1057 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1034 = false ∨ valuation q 1057 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) + (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (l₂ := [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_left (literal (valuationOf q) (981)) (literal (valuationOf q) (1055)) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 9 (meaning981 q) (meaning1055 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 1055 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1057 = true := by
  have hs : count1047 q = (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) + (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (l₂ := [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (981)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1057)) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85]) (countLit q [-86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1047 q) 9 2 (meaning981 q) (meaning1033 q) (meaning1057 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 1033 = false ∨ valuation q 1057 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) + (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (l₂ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 8 11 (meaning917 q) (meaning1057 q) (meaning1084 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 1057 = false ∨ valuation q 1084 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) + (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (l₂ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 9 10 (meaning918 q) (meaning1056 q) (meaning1084 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 1056 = false ∨ valuation q 1084 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) + (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (l₂ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (1055)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 10 9 (meaning919 q) (meaning1055 q) (meaning1084 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 1055 = false ∨ valuation q 1084 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) + (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (l₂ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (1054)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 11 8 (meaning920 q) (meaning1054 q) (meaning1084 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 1054 = false ∨ valuation q 1084 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) + (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (l₂ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (1053)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 12 7 (meaning921 q) (meaning1053 q) (meaning1084 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 1053 = false ∨ valuation q 1084 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) + (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (l₂ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (1052)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 13 6 (meaning922 q) (meaning1052 q) (meaning1084 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 1052 = false ∨ valuation q 1084 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) + (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (l₂ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (1051)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 14 5 (meaning923 q) (meaning1051 q) (meaning1084 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 1051 = false ∨ valuation q 1084 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) + (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (l₂ := [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (1050)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (countLit q [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -80, -84, -85, -86, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 15 4 (meaning924 q) (meaning1050 q) (meaning1084 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 1050 = false ∨ valuation q 1084 = true := counterClause1140 (baseVal q)

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false := by
  rw [value1084]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1066 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1412 = true := by
  have hs : count1411 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1412)) (countLit q [-4]) (countLit q [-5]) (count1411 q) 1 1 (meaningNeg4 q) (meaningNeg5 q) (meaning1412 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 1412 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1414 = true := by
  have hs : count1413 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1412)) (literal (valuationOf q) (1414)) (countLit q [-2]) (countLit q [-4, -5]) (count1413 q) 2 (meaning1412 q) (meaning1414 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1414 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1412 = false ∨ valuationOf q 1415 = true := by
  have hs : count1413 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1415)) (countLit q [-2]) (countLit q [-4, -5]) (count1413 q) 1 2 (meaningNeg2 q) (meaning1412 q) (meaning1415 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1412 = false ∨ valuation q 1415 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1416 = true := by
  have hs : count1416 q = (countLit q [-6]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1416)) (countLit q [-6]) (countLit q [-10]) (count1416 q) 1 (meaningNeg6 q) (meaning1416 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1416 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 10 = true ∨ valuationOf q 1417 = true := by
  have hs : count1416 q = (countLit q [-6]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (1417)) (countLit q [-6]) (countLit q [-10]) (count1416 q) 1 1 (meaningNeg6 q) (meaningNeg10 q) (meaning1417 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 10 = true ∨ valuation q 1417 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 12 = true ∨ valuationOf q 1419 = true := by
  have hs : count1418 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (1419)) (countLit q [-11]) (countLit q [-12]) (count1418 q) 1 1 (meaningNeg11 q) (meaningNeg12 q) (meaning1419 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 12 = true ∨ valuation q 1419 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1422 = true := by
  have hs : count1420 q = (countLit q [-6, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1422)) (countLit q [-6, -10]) (countLit q [-11, -12]) (count1420 q) 1 2 (meaning1416 q) (meaning1419 q) (meaning1422 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1419 = false ∨ valuation q 1422 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1423 = true := by
  have hs : count1420 q = (countLit q [-6, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1423)) (countLit q [-6, -10]) (countLit q [-11, -12]) (count1420 q) 2 2 (meaning1417 q) (meaning1419 q) (meaning1423 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1419 = false ∨ valuation q 1423 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1429 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1429)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 2 4 (meaning1414 q) (meaning1423 q) (meaning1429 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1423 = false ∨ valuation q 1429 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1429 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1429)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 3 3 (meaning1415 q) (meaning1422 q) (meaning1429 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1422 = false ∨ valuation q 1429 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1431 = true := by
  have hs : count1431 q = (countLit q [-18]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1431)) (countLit q [-18]) (countLit q [-21]) (count1431 q) 1 (meaningNeg18 q) (meaning1431 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1431 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E203.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112203
