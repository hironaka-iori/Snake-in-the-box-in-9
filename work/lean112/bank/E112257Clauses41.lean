import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) + (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (l₂ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1049 q) 11 7 (meaning910 q) (meaning1037 q) (meaning1066 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 1037 = false ∨ valuation q 1066 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) + (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (l₂ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (911)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1049 q) 12 6 (meaning911 q) (meaning1036 q) (meaning1066 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 1036 = false ∨ valuation q 1066 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) + (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (l₂ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (912)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1049 q) 13 5 (meaning912 q) (meaning1035 q) (meaning1066 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 1035 = false ∨ valuation q 1066 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 913 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) + (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (l₂ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (913)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1049 q) 14 4 (meaning913 q) (meaning1034 q) (meaning1066 q) hs
  change valuationOf q 913 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 913 = false ∨ valuation q 1034 = false ∨ valuation q 1066 = true := counterClause1316 (baseVal q)

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false := by
  rw [value1066]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1049 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1393 = true := by
  have hs : count1393 q = (countLit q [-5]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-8])
  have hm := merge_right (literal (valuationOf q) (-8)) (literal (valuationOf q) (1393)) (countLit q [-5]) (countLit q [-8]) (count1393 q) 1 (meaningNeg8 q) (meaning1393 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1393 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1393 = true := by
  have hs : count1393 q = (countLit q [-5]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-8])
  have hm := merge_left (literal (valuationOf q) (-5)) (literal (valuationOf q) (1393)) (countLit q [-5]) (countLit q [-8]) (count1393 q) 1 (meaningNeg5 q) (meaning1393 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1393 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 8 = true ∨ valuationOf q 1394 = true := by
  have hs : count1393 q = (countLit q [-5]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-8])
  have hm := merge_two (literal (valuationOf q) (-5)) (literal (valuationOf q) (-8)) (literal (valuationOf q) (1394)) (countLit q [-5]) (countLit q [-8]) (count1393 q) 1 1 (meaningNeg5 q) (meaningNeg8 q) (meaning1394 q) hs
  change (! (valuationOf q 5)) = false ∨ (! (valuationOf q 8)) = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 1394 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-3]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5, -8])
  have hm := merge_right (literal (valuationOf q) (1393)) (literal (valuationOf q) (1395)) (countLit q [-3]) (countLit q [-5, -8]) (count1395 q) 1 (meaning1393 q) (meaning1395 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1395 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1396 = true := by
  have hs : count1395 q = (countLit q [-3]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5, -8])
  have hm := merge_right (literal (valuationOf q) (1394)) (literal (valuationOf q) (1396)) (countLit q [-3]) (countLit q [-5, -8]) (count1395 q) 2 (meaning1394 q) (meaning1396 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1396 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-3]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5, -8])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1395)) (countLit q [-3]) (countLit q [-5, -8]) (count1395 q) 1 (meaningNeg3 q) (meaning1395 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1395 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1393 = false ∨ valuationOf q 1396 = true := by
  have hs : count1395 q = (countLit q [-3]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5, -8])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1396)) (countLit q [-3]) (countLit q [-5, -8]) (count1395 q) 1 1 (meaningNeg3 q) (meaning1393 q) (meaning1396 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1393 = false ∨ valuation q 1396 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (1398)) (countLit q [-9]) (countLit q [-10]) (count1398 q) 1 (meaningNeg10 q) (meaning1398 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1398 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1400 = true := by
  have hs : count1400 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_right (literal (valuationOf q) (-14)) (literal (valuationOf q) (1400)) (countLit q [-13]) (countLit q [-14]) (count1400 q) 1 (meaningNeg14 q) (meaning1400 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1400 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-9, -10]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-13, -14])
  have hm := merge_right (literal (valuationOf q) (1400)) (literal (valuationOf q) (1402)) (countLit q [-9, -10]) (countLit q [-13, -14]) (count1402 q) 1 (meaning1400 q) (meaning1402 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1402 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-9, -10]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-13, -14])
  have hm := merge_left (literal (valuationOf q) (1398)) (literal (valuationOf q) (1402)) (countLit q [-9, -10]) (countLit q [-13, -14]) (count1402 q) 1 (meaning1398 q) (meaning1402 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1402 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-3, -5, -8]) + (countLit q [-9, -10, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8]) (l₂ := [-9, -10, -13, -14])
  have hm := merge_right (literal (valuationOf q) (1402)) (literal (valuationOf q) (1406)) (countLit q [-3, -5, -8]) (countLit q [-9, -10, -13, -14]) (count1406 q) 1 (meaning1402 q) (meaning1406 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1406 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-3, -5, -8]) + (countLit q [-9, -10, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8]) (l₂ := [-9, -10, -13, -14])
  have hm := merge_left (literal (valuationOf q) (1395)) (literal (valuationOf q) (1406)) (countLit q [-3, -5, -8]) (countLit q [-9, -10, -13, -14]) (count1406 q) 1 (meaning1395 q) (meaning1406 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1406 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-3, -5, -8]) + (countLit q [-9, -10, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8]) (l₂ := [-9, -10, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1407)) (countLit q [-3, -5, -8]) (countLit q [-9, -10, -13, -14]) (count1406 q) 1 1 (meaning1395 q) (meaning1402 q) (meaning1407 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1402 = false ∨ valuation q 1407 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-3, -5, -8]) + (countLit q [-9, -10, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8]) (l₂ := [-9, -10, -13, -14])
  have hm := merge_left (literal (valuationOf q) (1396)) (literal (valuationOf q) (1407)) (countLit q [-3, -5, -8]) (countLit q [-9, -10, -13, -14]) (count1406 q) 2 (meaning1396 q) (meaning1407 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1407 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1408 = true := by
  have hs : count1406 q = (countLit q [-3, -5, -8]) + (countLit q [-9, -10, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8]) (l₂ := [-9, -10, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1408)) (countLit q [-3, -5, -8]) (countLit q [-9, -10, -13, -14]) (count1406 q) 2 1 (meaning1396 q) (meaning1402 q) (meaning1408 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1402 = false ∨ valuation q 1408 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1413 = true := by
  have hs : count1413 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (1413)) (countLit q [-18]) (countLit q [-20]) (count1413 q) 1 (meaningNeg20 q) (meaning1413 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1413 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1413 = true := by
  have hs : count1413 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1413)) (countLit q [-18]) (countLit q [-20]) (count1413 q) 1 (meaningNeg18 q) (meaning1413 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1413 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 20 = true ∨ valuationOf q 1414 = true := by
  have hs : count1413 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-20)) (literal (valuationOf q) (1414)) (countLit q [-18]) (countLit q [-20]) (count1413 q) 1 1 (meaningNeg18 q) (meaningNeg20 q) (meaning1414 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 20)) = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 20 = true ∨ valuation q 1414 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1415 = true := by
  have hs : count1415 q = (countLit q [-17]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18, -20])
  have hm := merge_right (literal (valuationOf q) (1413)) (literal (valuationOf q) (1415)) (countLit q [-17]) (countLit q [-18, -20]) (count1415 q) 1 (meaning1413 q) (meaning1415 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1415 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1416 = true := by
  have hs : count1415 q = (countLit q [-17]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18, -20])
  have hm := merge_right (literal (valuationOf q) (1414)) (literal (valuationOf q) (1416)) (countLit q [-17]) (countLit q [-18, -20]) (count1415 q) 2 (meaning1414 q) (meaning1416 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1416 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1415 = true := by
  have hs : count1415 q = (countLit q [-17]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18, -20])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1415)) (countLit q [-17]) (countLit q [-18, -20]) (count1415 q) 1 (meaningNeg17 q) (meaning1415 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1415 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1414 = false ∨ valuationOf q 1417 = true := by
  have hs : count1415 q = (countLit q [-17]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18, -20])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1417)) (countLit q [-17]) (countLit q [-18, -20]) (count1415 q) 1 2 (meaningNeg17 q) (meaning1414 q) (meaning1417 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1414 = false ∨ valuation q 1417 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1420 = true := by
  have hs : count1420 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_right (literal (valuationOf q) (-27)) (literal (valuationOf q) (1420)) (countLit q [-25]) (countLit q [-27]) (count1420 q) 1 (meaningNeg27 q) (meaning1420 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1420 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-22, -24]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-25, -27])
  have hm := merge_right (literal (valuationOf q) (1420)) (literal (valuationOf q) (1422)) (countLit q [-22, -24]) (countLit q [-25, -27]) (count1422 q) 1 (meaning1420 q) (meaning1422 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1422 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-17, -18, -20]) + (countLit q [-22, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-22, -24, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1422)) (literal (valuationOf q) (1426)) (countLit q [-17, -18, -20]) (countLit q [-22, -24, -25, -27]) (count1426 q) 1 (meaning1422 q) (meaning1426 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1426 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-17, -18, -20]) + (countLit q [-22, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-22, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1415)) (literal (valuationOf q) (1426)) (countLit q [-17, -18, -20]) (countLit q [-22, -24, -25, -27]) (count1426 q) 1 (meaning1415 q) (meaning1426 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1426 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E257.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112257
