import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1030 = true := by
  have hs : count1024 q = (countLit q [-105, -106, -107, -110]) + (countLit q [-112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -110]) (l₂ := [-112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1030)) (countLit q [-105, -106, -107, -110]) (countLit q [-112, -114, -115, -117]) (count1024 q) 3 4 (meaning1014 q) (meaning1023 q) (meaning1030 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1030 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1023 = false ∨ valuation q 1030 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1026 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-91, -92, -93, -96, -99, -100, -102]) + (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -93, -96, -99, -100, -102]) (l₂ := [-105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1026)) (literal (valuationOf q) (1034)) (countLit q [-91, -92, -93, -96, -99, -100, -102]) (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) (count1032 q) 3 (meaning1026 q) (meaning1034 q) hs
  change valuationOf q 1026 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1026 = false ∨ valuation q 1034 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1027 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-91, -92, -93, -96, -99, -100, -102]) + (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -93, -96, -99, -100, -102]) (l₂ := [-105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1027)) (literal (valuationOf q) (1035)) (countLit q [-91, -92, -93, -96, -99, -100, -102]) (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) (count1032 q) 4 (meaning1027 q) (meaning1035 q) hs
  change valuationOf q 1027 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1027 = false ∨ valuation q 1035 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1028 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-91, -92, -93, -96, -99, -100, -102]) + (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -93, -96, -99, -100, -102]) (l₂ := [-105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1028)) (literal (valuationOf q) (1036)) (countLit q [-91, -92, -93, -96, -99, -100, -102]) (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) (count1032 q) 5 (meaning1028 q) (meaning1036 q) hs
  change valuationOf q 1028 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1028 = false ∨ valuation q 1036 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1029 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-91, -92, -93, -96, -99, -100, -102]) + (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -93, -96, -99, -100, -102]) (l₂ := [-105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1029)) (literal (valuationOf q) (1037)) (countLit q [-91, -92, -93, -96, -99, -100, -102]) (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) (count1032 q) 6 (meaning1029 q) (meaning1037 q) hs
  change valuationOf q 1029 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1029 = false ∨ valuation q 1037 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1030 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-91, -92, -93, -96, -99, -100, -102]) + (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -93, -96, -99, -100, -102]) (l₂ := [-105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1030)) (literal (valuationOf q) (1038)) (countLit q [-91, -92, -93, -96, -99, -100, -102]) (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) (count1032 q) 7 (meaning1030 q) (meaning1038 q) hs
  change valuationOf q 1030 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1030 = false ∨ valuation q 1038 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-91, -92, -93, -96, -99, -100, -102]) + (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -93, -96, -99, -100, -102]) (l₂ := [-105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1035)) (countLit q [-91, -92, -93, -96, -99, -100, -102]) (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) (count1032 q) 1 3 (meaning1001 q) (meaning1026 q) (meaning1035 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1026 = false ∨ valuation q 1035 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-91, -92, -93, -96, -99, -100, -102]) + (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -93, -96, -99, -100, -102]) (l₂ := [-105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1036)) (countLit q [-91, -92, -93, -96, -99, -100, -102]) (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) (count1032 q) 1 4 (meaning1001 q) (meaning1027 q) (meaning1036 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1027 = false ∨ valuation q 1036 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-91, -92, -93, -96, -99, -100, -102]) + (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -93, -96, -99, -100, -102]) (l₂ := [-105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1037)) (countLit q [-91, -92, -93, -96, -99, -100, -102]) (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) (count1032 q) 1 5 (meaning1001 q) (meaning1028 q) (meaning1037 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1028 = false ∨ valuation q 1037 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-91, -92, -93, -96, -99, -100, -102]) + (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -93, -96, -99, -100, -102]) (l₂ := [-105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1038)) (countLit q [-91, -92, -93, -96, -99, -100, -102]) (countLit q [-105, -106, -107, -110, -112, -114, -115, -117]) (count1032 q) 1 6 (meaning1001 q) (meaning1029 q) (meaning1038 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1029 = false ∨ valuation q 1038 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1051 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1051)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 1 4 (meaning973 q) (meaning1035 q) (meaning1051 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1035 = false ∨ valuation q 1051 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1052)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 1 5 (meaning973 q) (meaning1036 q) (meaning1052 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1036 = false ∨ valuation q 1052 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1053)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 1 6 (meaning973 q) (meaning1037 q) (meaning1053 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1037 = false ∨ valuation q 1053 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1054)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 1 7 (meaning973 q) (meaning1038 q) (meaning1054 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1038 = false ∨ valuation q 1054 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1051 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1051)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 2 3 (meaning974 q) (meaning1034 q) (meaning1051 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1034 = false ∨ valuation q 1051 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1052)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 2 4 (meaning974 q) (meaning1035 q) (meaning1052 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1035 = false ∨ valuation q 1052 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1053)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 2 5 (meaning974 q) (meaning1036 q) (meaning1053 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1036 = false ∨ valuation q 1053 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1054)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 2 6 (meaning974 q) (meaning1037 q) (meaning1054 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1037 = false ∨ valuation q 1054 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1052)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 3 3 (meaning975 q) (meaning1034 q) (meaning1052 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1034 = false ∨ valuation q 1052 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1053)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 3 4 (meaning975 q) (meaning1035 q) (meaning1053 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1035 = false ∨ valuation q 1053 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1054)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 3 5 (meaning975 q) (meaning1036 q) (meaning1054 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1036 = false ∨ valuation q 1054 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1055)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 3 6 (meaning975 q) (meaning1037 q) (meaning1055 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1037 = false ∨ valuation q 1055 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1056)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 3 7 (meaning975 q) (meaning1038 q) (meaning1056 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1038 = false ∨ valuation q 1056 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1053)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 4 3 (meaning976 q) (meaning1034 q) (meaning1053 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1034 = false ∨ valuation q 1053 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1054)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 4 4 (meaning976 q) (meaning1035 q) (meaning1054 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1035 = false ∨ valuation q 1054 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1055)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 4 5 (meaning976 q) (meaning1036 q) (meaning1055 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1036 = false ∨ valuation q 1055 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1056)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 4 6 (meaning976 q) (meaning1037 q) (meaning1056 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1037 = false ∨ valuation q 1056 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1054 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1054)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 5 3 (meaning977 q) (meaning1034 q) (meaning1054 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1034 = false ∨ valuation q 1054 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1055 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1055)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 5 4 (meaning977 q) (meaning1035 q) (meaning1055 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1035 = false ∨ valuation q 1055 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1056 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1056)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 5 5 (meaning977 q) (meaning1036 q) (meaning1056 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1036 = false ∨ valuation q 1056 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1057 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1057)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 5 6 (meaning977 q) (meaning1037 q) (meaning1057 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1037 = false ∨ valuation q 1057 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1058 = true := by
  have hs : count1047 q = (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) + (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (l₂ := [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1058)) (countLit q [-61, -62, -65, -67, -68, -70, -73, -74, -75, -78, -79, -82, -84, -86, -88]) (countLit q [-91, -92, -93, -96, -99, -100, -102, -105, -106, -107, -110, -112, -114, -115, -117]) (count1047 q) 5 7 (meaning977 q) (meaning1038 q) (meaning1058 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1038 = false ∨ valuation q 1058 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E115.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112115
