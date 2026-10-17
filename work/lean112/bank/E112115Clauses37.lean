import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1055)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 6 3 (meaning978 q) (meaning1034 q) (meaning1055 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1034 = false ∨ valuation q 1055 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1056)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 6 4 (meaning978 q) (meaning1035 q) (meaning1056 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1035 = false ∨ valuation q 1056 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1057 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1057)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 6 5 (meaning978 q) (meaning1036 q) (meaning1057 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1036 = false ∨ valuation q 1057 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1058 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1058)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 6 6 (meaning978 q) (meaning1037 q) (meaning1058 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1037 = false ∨ valuation q 1058 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1059 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1059)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 6 7 (meaning978 q) (meaning1038 q) (meaning1059 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1038 = false ∨ valuation q 1059 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1056)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 7 3 (meaning979 q) (meaning1034 q) (meaning1056 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1034 = false ∨ valuation q 1056 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1057 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1057)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 7 4 (meaning979 q) (meaning1035 q) (meaning1057 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1035 = false ∨ valuation q 1057 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1058 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1058)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 7 5 (meaning979 q) (meaning1036 q) (meaning1058 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1036 = false ∨ valuation q 1058 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1059 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1059)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 7 6 (meaning979 q) (meaning1037 q) (meaning1059 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1037 = false ∨ valuation q 1059 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1057 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1057)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 8 3 (meaning980 q) (meaning1034 q) (meaning1057 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1034 = false ∨ valuation q 1057 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1058 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1058)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 8 4 (meaning980 q) (meaning1035 q) (meaning1058 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1035 = false ∨ valuation q 1058 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1059 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1059)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 8 5 (meaning980 q) (meaning1036 q) (meaning1059 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1036 = false ∨ valuation q 1059 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1059 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (981)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1059)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 9 4 (meaning981 q) (meaning1035 q) (meaning1059 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 1035 = false ∨ valuation q 1059 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 915 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) + (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (l₂ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (915)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1084)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1066 q) 6 13 (meaning915 q) (meaning1059 q) (meaning1084 q) hs
  change valuationOf q 915 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 915 = false ∨ valuation q 1059 = false ∨ valuation q 1084 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) + (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (l₂ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1084)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1066 q) 7 12 (meaning916 q) (meaning1058 q) (meaning1084 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 1058 = false ∨ valuation q 1084 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) + (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (l₂ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1084)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1066 q) 8 11 (meaning917 q) (meaning1057 q) (meaning1084 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 1057 = false ∨ valuation q 1084 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) + (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (l₂ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1084)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1066 q) 9 10 (meaning918 q) (meaning1056 q) (meaning1084 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 1056 = false ∨ valuation q 1084 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) + (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (l₂ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (1055)) (literal (valuationOf q) (1084)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1066 q) 10 9 (meaning919 q) (meaning1055 q) (meaning1084 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 1055 = false ∨ valuation q 1084 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) + (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (l₂ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (1054)) (literal (valuationOf q) (1084)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1066 q) 11 8 (meaning920 q) (meaning1054 q) (meaning1084 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 1054 = false ∨ valuation q 1084 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) + (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (l₂ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (1053)) (literal (valuationOf q) (1084)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1066 q) 12 7 (meaning921 q) (meaning1053 q) (meaning1084 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 1053 = false ∨ valuation q 1084 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) + (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (l₂ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (1052)) (literal (valuationOf q) (1084)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1066 q) 13 6 (meaning922 q) (meaning1052 q) (meaning1084 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 1052 = false ∨ valuation q 1084 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) + (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (l₂ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (1051)) (literal (valuationOf q) (1084)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25, -28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88, -91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1066 q) 14 5 (meaning923 q) (meaning1051 q) (meaning1084 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 1051 = false ∨ valuation q 1084 = true := counterClause1206 (baseVal q)

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false := by
  rw [value1084]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1066 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 4 = false := by
  rw [value1, value2, value3, value4]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (2 : Vertex) (3 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 6 = false ∨ valuation q 7 = false := by
  rw [value1, value2, value6, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (8 : Vertex) (9 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 12 = false ∨ valuation q 13 = false := by
  rw [value1, value2, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (16 : Vertex) (17 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 12 = false ∨ valuation q 14 = false := by
  rw [value1, value3, value12, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (2 : Vertex) (16 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 7 = false ∨ valuation q 74 = false ∨ valuation q 80 = false := by
  rw [value2, value7, value74, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (1 : Vertex) (9 : Vertex) (257 : Vertex) (265 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 24 = false ∨ valuation q 39 = false ∨ valuation q 57 = false := by
  rw [value2, value24, value39, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (1 : Vertex) (65 : Vertex) (129 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 11 = false := by
  rw [value4, value5, value8, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (3 : Vertex) (7 : Vertex) (11 : Vertex) (15 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 10 = false := by
  rw [value6, value7, value9, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (8 : Vertex) (9 : Vertex) (12 : Vertex) (13 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 9 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value6, value9, value18, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (8 : Vertex) (12 : Vertex) (24 : Vertex) (28 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E115.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112115
