import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1056)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 5 5 (meaning977 q) (meaning1036 q) (meaning1056 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1036 = false ∨ valuation q 1056 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1055)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 6 3 (meaning978 q) (meaning1034 q) (meaning1055 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1034 = false ∨ valuation q 1055 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1056)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 6 4 (meaning978 q) (meaning1035 q) (meaning1056 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1035 = false ∨ valuation q 1056 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1057 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1057)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 6 5 (meaning978 q) (meaning1036 q) (meaning1057 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1036 = false ∨ valuation q 1057 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1055)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 7 2 (meaning979 q) (meaning1033 q) (meaning1055 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1033 = false ∨ valuation q 1055 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1056)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 7 3 (meaning979 q) (meaning1034 q) (meaning1056 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1034 = false ∨ valuation q 1056 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1057 = true := by
  have hs : count1047 q = (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) + (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (l₂ := [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1057)) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90]) (countLit q [-91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1047 q) 7 4 (meaning979 q) (meaning1035 q) (meaning1057 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1035 = false ∨ valuation q 1057 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) + (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (l₂ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1066 q) 8 11 (meaning917 q) (meaning1057 q) (meaning1084 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 1057 = false ∨ valuation q 1084 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) + (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (l₂ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1066 q) 9 10 (meaning918 q) (meaning1056 q) (meaning1084 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 1056 = false ∨ valuation q 1084 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) + (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (l₂ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (1055)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1066 q) 10 9 (meaning919 q) (meaning1055 q) (meaning1084 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 1055 = false ∨ valuation q 1084 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) + (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (l₂ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (1054)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1066 q) 11 8 (meaning920 q) (meaning1054 q) (meaning1084 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 1054 = false ∨ valuation q 1084 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) + (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (l₂ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (1053)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1066 q) 12 7 (meaning921 q) (meaning1053 q) (meaning1084 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 1053 = false ∨ valuation q 1084 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) + (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (l₂ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (1052)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1066 q) 13 6 (meaning922 q) (meaning1052 q) (meaning1084 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 1052 = false ∨ valuation q 1084 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) + (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (l₂ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (1051)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1066 q) 14 5 (meaning923 q) (meaning1051 q) (meaning1084 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 1051 = false ∨ valuation q 1084 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) + (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (l₂ := [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (1050)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25, -27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (countLit q [-59, -62, -64, -66, -69, -72, -73, -74, -76, -79, -81, -83, -84, -87, -90, -91, -93, -94, -97, -99, -100, -101, -103, -104, -105, -108, -110, -113, -116, -117]) (count1066 q) 15 4 (meaning924 q) (meaning1050 q) (meaning1084 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 1050 = false ∨ valuation q 1084 = true := counterClause1167 (baseVal q)

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false := by
  rw [value1084]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1066 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value1, value2, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (128 : Vertex) (129 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 23 = false := by
  rw [value4, value6, value21, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (8 : Vertex) (12 : Vertex) (72 : Vertex) (76 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 34 = false := by
  rw [value5, value13, value22, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (11 : Vertex) (27 : Vertex) (75 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 25 = false := by
  rw [value6, value7, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (12 : Vertex) (14 : Vertex) (76 : Vertex) (78 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 29 = false ∨ valuation q 48 = false ∨ valuation q 66 = false := by
  rw [value8, value29, value48, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (18 : Vertex) (82 : Vertex) (146 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 18 = false := by
  rw [value15, value16, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (64 : Vertex) (65 : Vertex) (66 : Vertex) (67 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value15, value16, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (64 : Vertex) (65 : Vertex) (320 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 27 = false ∨ valuation q 29 = false := by
  rw [value15, value17, value27, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (64 : Vertex) (66 : Vertex) (80 : Vertex) (82 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 28 = false ∨ valuation q 30 = false := by
  rw [value16, value18, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (65 : Vertex) (67 : Vertex) (81 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value17, value18, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (66 : Vertex) (67 : Vertex) (82 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 26 = false := by
  rw [value18, value20, value22, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (67 : Vertex) (71 : Vertex) (75 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value19, value20, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (69 : Vertex) (71 : Vertex) (77 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 61 = false ∨ valuation q 64 = false := by
  rw [value21, value23, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (72 : Vertex) (76 : Vertex) (200 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 78 = false ∨ valuation q 81 = false := by
  rw [value21, value23, value78, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (72 : Vertex) (76 : Vertex) (328 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 26 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value22, value26, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (75 : Vertex) (79 : Vertex) (91 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 34 = false ∨ valuation q 63 = false ∨ valuation q 72 = false := by
  rw [value22, value34, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (75 : Vertex) (91 : Vertex) (203 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E213.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112213
