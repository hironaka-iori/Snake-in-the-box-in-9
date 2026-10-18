import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 1019 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (988)) (literal (valuationOf q) (1019)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 4 (meaning988 q) (meaning1019 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 1019 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1020 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (988)) (literal (valuationOf q) (1008)) (literal (valuationOf q) (1020)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 4 1 (meaning988 q) (meaning1008 q) (meaning1020 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 1008 = false ∨ valuation q 1020 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1021 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (988)) (literal (valuationOf q) (1009)) (literal (valuationOf q) (1021)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 4 2 (meaning988 q) (meaning1009 q) (meaning1021 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 1009 = false ∨ valuation q 1021 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1022 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (988)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1022)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 4 3 (meaning988 q) (meaning1010 q) (meaning1022 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 1010 = false ∨ valuation q 1022 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1023 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (988)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1023)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 4 4 (meaning988 q) (meaning1011 q) (meaning1023 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1023 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 1011 = false ∨ valuation q 1023 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 989 = false ∨ valuationOf q 1020 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (989)) (literal (valuationOf q) (1020)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 5 (meaning989 q) (meaning1020 q) hs
  change valuationOf q 989 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 989 = false ∨ valuation q 1020 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 989 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1021 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (989)) (literal (valuationOf q) (1008)) (literal (valuationOf q) (1021)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 5 1 (meaning989 q) (meaning1008 q) (meaning1021 q) hs
  change valuationOf q 989 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 989 = false ∨ valuation q 1008 = false ∨ valuation q 1021 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 989 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1022 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (989)) (literal (valuationOf q) (1009)) (literal (valuationOf q) (1022)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 5 2 (meaning989 q) (meaning1009 q) (meaning1022 q) hs
  change valuationOf q 989 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 989 = false ∨ valuation q 1009 = false ∨ valuation q 1022 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 989 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1023 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (989)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1023)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 5 3 (meaning989 q) (meaning1010 q) (meaning1023 q) hs
  change valuationOf q 989 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1023 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 989 = false ∨ valuation q 1010 = false ∨ valuation q 1023 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 989 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1024 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (989)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1024)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 5 4 (meaning989 q) (meaning1011 q) (meaning1024 q) hs
  change valuationOf q 989 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 989 = false ∨ valuation q 1011 = false ∨ valuation q 1024 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1031 = true := by
  have hs : count1031 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_right (literal (valuationOf q) (-95)) (literal (valuationOf q) (1031)) (countLit q [-94]) (countLit q [-95]) (count1031 q) 1 (meaningNeg95 q) (meaning1031 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1031 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1031 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1031 = true := by
  have hs : count1031 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1031)) (countLit q [-94]) (countLit q [-95]) (count1031 q) 1 (meaningNeg94 q) (meaning1031 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1031 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1031 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 95 = true ∨ valuationOf q 1032 = true := by
  have hs : count1031 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-95)) (literal (valuationOf q) (1032)) (countLit q [-94]) (countLit q [-95]) (count1031 q) 1 1 (meaningNeg94 q) (meaningNeg95 q) (meaning1032 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 95)) = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 95 = true ∨ valuation q 1032 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1033 = true := by
  have hs : count1033 q = (countLit q [-97]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1033)) (countLit q [-97]) (countLit q [-100]) (count1033 q) 1 (meaningNeg100 q) (meaning1033 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1033 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1033 = true := by
  have hs : count1033 q = (countLit q [-97]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1033)) (countLit q [-97]) (countLit q [-100]) (count1033 q) 1 (meaningNeg97 q) (meaning1033 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1033 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1034 = true := by
  have hs : count1033 q = (countLit q [-97]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1034)) (countLit q [-97]) (countLit q [-100]) (count1033 q) 1 1 (meaningNeg97 q) (meaningNeg100 q) (meaning1034 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 100 = true ∨ valuation q 1034 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1035 = true := by
  have hs : count1035 q = (countLit q [-94, -95]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-97, -100])
  have hm := merge_right (literal (valuationOf q) (1033)) (literal (valuationOf q) (1035)) (countLit q [-94, -95]) (countLit q [-97, -100]) (count1035 q) 1 (meaning1033 q) (meaning1035 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1035 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1036 = true := by
  have hs : count1035 q = (countLit q [-94, -95]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-97, -100])
  have hm := merge_right (literal (valuationOf q) (1034)) (literal (valuationOf q) (1036)) (countLit q [-94, -95]) (countLit q [-97, -100]) (count1035 q) 2 (meaning1034 q) (meaning1036 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1036 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1031 = false ∨ valuationOf q 1035 = true := by
  have hs : count1035 q = (countLit q [-94, -95]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-97, -100])
  have hm := merge_left (literal (valuationOf q) (1031)) (literal (valuationOf q) (1035)) (countLit q [-94, -95]) (countLit q [-97, -100]) (count1035 q) 1 (meaning1031 q) (meaning1035 q) hs
  change valuationOf q 1031 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1031 = false ∨ valuation q 1035 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1031 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1036 = true := by
  have hs : count1035 q = (countLit q [-94, -95]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-97, -100])
  have hm := merge_two (literal (valuationOf q) (1031)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1036)) (countLit q [-94, -95]) (countLit q [-97, -100]) (count1035 q) 1 1 (meaning1031 q) (meaning1033 q) (meaning1036 q) hs
  change valuationOf q 1031 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1031 = false ∨ valuation q 1033 = false ∨ valuation q 1036 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1031 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1037 = true := by
  have hs : count1035 q = (countLit q [-94, -95]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-97, -100])
  have hm := merge_two (literal (valuationOf q) (1031)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1037)) (countLit q [-94, -95]) (countLit q [-97, -100]) (count1035 q) 1 2 (meaning1031 q) (meaning1034 q) (meaning1037 q) hs
  change valuationOf q 1031 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1031 = false ∨ valuation q 1034 = false ∨ valuation q 1037 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1036 = true := by
  have hs : count1035 q = (countLit q [-94, -95]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-97, -100])
  have hm := merge_left (literal (valuationOf q) (1032)) (literal (valuationOf q) (1036)) (countLit q [-94, -95]) (countLit q [-97, -100]) (count1035 q) 2 (meaning1032 q) (meaning1036 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1036 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1037 = true := by
  have hs : count1035 q = (countLit q [-94, -95]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-97, -100])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1037)) (countLit q [-94, -95]) (countLit q [-97, -100]) (count1035 q) 2 1 (meaning1032 q) (meaning1033 q) (meaning1037 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1033 = false ∨ valuation q 1037 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1038 = true := by
  have hs : count1035 q = (countLit q [-94, -95]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-97, -100])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1038)) (countLit q [-94, -95]) (countLit q [-97, -100]) (count1035 q) 2 2 (meaning1032 q) (meaning1034 q) (meaning1038 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1034 = false ∨ valuation q 1038 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1039 = true := by
  have hs : count1039 q = (countLit q [-101]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1039)) (countLit q [-101]) (countLit q [-105]) (count1039 q) 1 (meaningNeg105 q) (meaning1039 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1039 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1039 = true := by
  have hs : count1039 q = (countLit q [-101]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1039)) (countLit q [-101]) (countLit q [-105]) (count1039 q) 1 (meaningNeg101 q) (meaning1039 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1039 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1040 = true := by
  have hs : count1039 q = (countLit q [-101]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-101)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1040)) (countLit q [-101]) (countLit q [-105]) (count1039 q) 1 1 (meaningNeg101 q) (meaningNeg105 q) (meaning1040 q) hs
  change (! (valuationOf q 101)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 105 = true ∨ valuation q 1040 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1041 = true := by
  have hs : count1041 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1041)) (countLit q [-106]) (countLit q [-108]) (count1041 q) 1 (meaningNeg108 q) (meaning1041 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1041 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1041 = true := by
  have hs : count1041 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1041)) (countLit q [-106]) (countLit q [-108]) (count1041 q) 1 (meaningNeg106 q) (meaning1041 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1041 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1042 = true := by
  have hs : count1041 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-106)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1042)) (countLit q [-106]) (countLit q [-108]) (count1041 q) 1 1 (meaningNeg106 q) (meaningNeg108 q) (meaning1042 q) hs
  change (! (valuationOf q 106)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1042 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 1042 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1041 = false ∨ valuationOf q 1043 = true := by
  have hs : count1043 q = (countLit q [-101, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -105]) (l₂ := [-106, -108])
  have hm := merge_right (literal (valuationOf q) (1041)) (literal (valuationOf q) (1043)) (countLit q [-101, -105]) (countLit q [-106, -108]) (count1043 q) 1 (meaning1041 q) (meaning1043 q) hs
  change valuationOf q 1041 = false ∨ valuationOf q 1043 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1041 = false ∨ valuation q 1043 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1042 = false ∨ valuationOf q 1044 = true := by
  have hs : count1043 q = (countLit q [-101, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -105]) (l₂ := [-106, -108])
  have hm := merge_right (literal (valuationOf q) (1042)) (literal (valuationOf q) (1044)) (countLit q [-101, -105]) (countLit q [-106, -108]) (count1043 q) 2 (meaning1042 q) (meaning1044 q) hs
  change valuationOf q 1042 = false ∨ valuationOf q 1044 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1042 = false ∨ valuation q 1044 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E097.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112097
