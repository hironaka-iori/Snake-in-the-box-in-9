import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 905 = false ∨ valuationOf q 1042 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) + (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (l₂ := [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (905)) (literal (valuationOf q) (1042)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) (count1049 q) 6 12 (meaning905 q) (meaning1042 q) (meaning1066 q) hs
  change valuationOf q 905 = false ∨ valuationOf q 1042 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 905 = false ∨ valuation q 1042 = false ∨ valuation q 1066 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) + (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (l₂ := [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (1041)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) (count1049 q) 7 11 (meaning906 q) (meaning1041 q) (meaning1066 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 1041 = false ∨ valuation q 1066 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) + (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (l₂ := [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (1040)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) (count1049 q) 8 10 (meaning907 q) (meaning1040 q) (meaning1066 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 1040 = false ∨ valuation q 1066 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) + (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (l₂ := [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (1039)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) (count1049 q) 9 9 (meaning908 q) (meaning1039 q) (meaning1066 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 1039 = false ∨ valuation q 1066 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) + (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (l₂ := [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) (count1049 q) 10 8 (meaning909 q) (meaning1038 q) (meaning1066 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 1038 = false ∨ valuation q 1066 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) + (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (l₂ := [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) (count1049 q) 11 7 (meaning910 q) (meaning1037 q) (meaning1066 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 1037 = false ∨ valuation q 1066 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) + (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (l₂ := [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (911)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) (count1049 q) 12 6 (meaning911 q) (meaning1036 q) (meaning1066 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 1036 = false ∨ valuation q 1066 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) + (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (l₂ := [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (912)) (literal (valuationOf q) (1035)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]) (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) (count1049 q) 13 5 (meaning912 q) (meaning1035 q) (meaning1066 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 1035 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 1035 = false ∨ valuation q 1066 = true := counterClause1320 (baseVal q)

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false := by
  rw [value1066]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1049 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1393 = true := by
  have hs : count1393 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1393)) (countLit q [-4]) (countLit q [-5]) (count1393 q) 1 (meaningNeg5 q) (meaning1393 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1393 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1393 = true := by
  have hs : count1393 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1393)) (countLit q [-4]) (countLit q [-5]) (count1393 q) 1 (meaningNeg4 q) (meaning1393 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1393 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1394 = true := by
  have hs : count1393 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1394)) (countLit q [-4]) (countLit q [-5]) (count1393 q) 1 1 (meaningNeg4 q) (meaningNeg5 q) (meaning1394 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 1394 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1393)) (literal (valuationOf q) (1395)) (countLit q [-3]) (countLit q [-4, -5]) (count1395 q) 1 (meaning1393 q) (meaning1395 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1395 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1396 = true := by
  have hs : count1395 q = (countLit q [-3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1394)) (literal (valuationOf q) (1396)) (countLit q [-3]) (countLit q [-4, -5]) (count1395 q) 2 (meaning1394 q) (meaning1396 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1396 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1395)) (countLit q [-3]) (countLit q [-4, -5]) (count1395 q) 1 (meaningNeg3 q) (meaning1395 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1395 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1393 = false ∨ valuationOf q 1396 = true := by
  have hs : count1395 q = (countLit q [-3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1396)) (countLit q [-3]) (countLit q [-4, -5]) (count1395 q) 1 1 (meaningNeg3 q) (meaning1393 q) (meaning1396 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1393 = false ∨ valuation q 1396 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1394 = false ∨ valuationOf q 1397 = true := by
  have hs : count1395 q = (countLit q [-3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1397)) (countLit q [-3]) (countLit q [-4, -5]) (count1395 q) 1 2 (meaningNeg3 q) (meaning1394 q) (meaning1397 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1394 = false ∨ valuation q 1397 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_right (literal (valuationOf q) (-9)) (literal (valuationOf q) (1398)) (countLit q [-8]) (countLit q [-9]) (count1398 q) 1 (meaningNeg9 q) (meaning1398 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1398 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1398)) (countLit q [-8]) (countLit q [-9]) (count1398 q) 1 (meaningNeg8 q) (meaning1398 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1398 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 9 = true ∨ valuationOf q 1399 = true := by
  have hs : count1398 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-9)) (literal (valuationOf q) (1399)) (countLit q [-8]) (countLit q [-9]) (count1398 q) 1 1 (meaningNeg8 q) (meaningNeg9 q) (meaning1399 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 9)) = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 9 = true ∨ valuation q 1399 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1400 = true := by
  have hs : count1400 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1400)) (countLit q [-12]) (countLit q [-13]) (count1400 q) 1 (meaningNeg13 q) (meaning1400 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1400 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1400 = true := by
  have hs : count1400 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-12)) (literal (valuationOf q) (1400)) (countLit q [-12]) (countLit q [-13]) (count1400 q) 1 (meaningNeg12 q) (meaning1400 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1400 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1401 = true := by
  have hs : count1400 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1401)) (countLit q [-12]) (countLit q [-13]) (count1400 q) 1 1 (meaningNeg12 q) (meaningNeg13 q) (meaning1401 q) hs
  change (! (valuationOf q 12)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 1401 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1400)) (literal (valuationOf q) (1402)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1402 q) 1 (meaning1400 q) (meaning1402 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1402 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1403 = true := by
  have hs : count1402 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1401)) (literal (valuationOf q) (1403)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1402 q) 2 (meaning1401 q) (meaning1403 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1403 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_left (literal (valuationOf q) (1398)) (literal (valuationOf q) (1402)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1402 q) 1 (meaning1398 q) (meaning1402 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1402 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1403 = true := by
  have hs : count1402 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuationOf q) (1398)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1403)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1402 q) 1 1 (meaning1398 q) (meaning1400 q) (meaning1403 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1400 = false ∨ valuation q 1403 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1404 = true := by
  have hs : count1402 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuationOf q) (1398)) (literal (valuationOf q) (1401)) (literal (valuationOf q) (1404)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1402 q) 1 2 (meaning1398 q) (meaning1401 q) (meaning1404 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1401 = false ∨ valuation q 1404 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1403 = true := by
  have hs : count1402 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_left (literal (valuationOf q) (1399)) (literal (valuationOf q) (1403)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1402 q) 2 (meaning1399 q) (meaning1403 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1403 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_right (literal (valuationOf q) (1402)) (literal (valuationOf q) (1406)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1406 q) 1 (meaning1402 q) (meaning1406 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1406 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_right (literal (valuationOf q) (1403)) (literal (valuationOf q) (1407)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1406 q) 2 (meaning1403 q) (meaning1407 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1407 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1395)) (literal (valuationOf q) (1406)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1406 q) 1 (meaning1395 q) (meaning1406 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1406 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E259.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112259
