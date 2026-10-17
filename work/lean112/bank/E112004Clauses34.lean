import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1021 = true := by
  have hs : count1020 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1021)) (countLit q [-104]) (countLit q [-107]) (count1020 q) 1 1 (meaningNeg104 q) (meaningNeg107 q) (meaning1021 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 107 = true ∨ valuation q 1021 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1021 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-104, -107]) + (countLit q [-110, -112]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-110, -112])
  have hm := merge_left (literal (valuationOf q) (1021)) (literal (valuationOf q) (1025)) (countLit q [-104, -107]) (countLit q [-110, -112]) (count1024 q) 2 (meaning1021 q) (meaning1025 q) hs
  change valuationOf q 1021 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1021 = false ∨ valuation q 1025 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 1030 = true := by
  have hs : count1030 q = (countLit q [-118]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-120])
  have hm := merge_right (literal (valuationOf q) (-120)) (literal (valuationOf q) (1030)) (countLit q [-118]) (countLit q [-120]) (count1030 q) 1 (meaningNeg120 q) (meaning1030 q) hs
  change (! (valuationOf q 120)) = false ∨ valuationOf q 1030 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 1030 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1030 = false ∨ valuationOf q 1032 = true := by
  have hs : count1032 q = (countLit q [-113, -115]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-113, -115]) (l₂ := [-118, -120])
  have hm := merge_right (literal (valuationOf q) (1030)) (literal (valuationOf q) (1032)) (countLit q [-113, -115]) (countLit q [-118, -120]) (count1032 q) 1 (meaning1030 q) (meaning1032 q) hs
  change valuationOf q 1030 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1030 = false ∨ valuation q 1032 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1025 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1038 = true := by
  have hs : count1036 q = (countLit q [-104, -107, -110, -112]) + (countLit q [-113, -115, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -110, -112]) (l₂ := [-113, -115, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1025)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1038)) (countLit q [-104, -107, -110, -112]) (countLit q [-113, -115, -118, -120]) (count1036 q) 2 1 (meaning1025 q) (meaning1032 q) (meaning1038 q) hs
  change valuationOf q 1025 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1025 = false ∨ valuation q 1032 = false ∨ valuation q 1038 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1050 = true := by
  have hs : count1044 q = (countLit q [-92, -93, -94, -95, -96, -99, -100]) + (countLit q [-104, -107, -110, -112, -113, -115, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94, -95, -96, -99, -100]) (l₂ := [-104, -107, -110, -112, -113, -115, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1050)) (countLit q [-92, -93, -94, -95, -96, -99, -100]) (countLit q [-104, -107, -110, -112, -113, -115, -118, -120]) (count1044 q) 4 3 (meaning1016 q) (meaning1038 q) (meaning1050 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1038 = false ∨ valuation q 1050 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1071 = true := by
  have hs : count1059 q = (countLit q [-58, -63, -65, -66, -68, -69, -72, -74, -76, -77, -79, -81, -85, -88, -89]) + (countLit q [-92, -93, -94, -95, -96, -99, -100, -104, -107, -110, -112, -113, -115, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-58, -63, -65, -66, -68, -69, -72, -74, -76, -77, -79, -81, -85, -88, -89]) (l₂ := [-92, -93, -94, -95, -96, -99, -100, -104, -107, -110, -112, -113, -115, -118, -120])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (1050)) (literal (valuationOf q) (1071)) (countLit q [-58, -63, -65, -66, -68, -69, -72, -74, -76, -77, -79, -81, -85, -88, -89]) (countLit q [-92, -93, -94, -95, -96, -99, -100, -104, -107, -110, -112, -113, -115, -118, -120]) (count1059 q) 6 7 (meaning990 q) (meaning1050 q) (meaning1071 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1071 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 1050 = false ∨ valuation q 1071 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 927 = false ∨ valuationOf q 1071 = false ∨ valuationOf q 1096 = true := by
  have hs : count1078 q = (countLit q [-1, -4, -7, -8, -9, -10, -11, -14, -16, -17, -19, -23, -25, -27, -29, -31, -33, -34, -37, -39, -41, -43, -45, -47, -49, -50, -54, -55, -57]) + (countLit q [-58, -63, -65, -66, -68, -69, -72, -74, -76, -77, -79, -81, -85, -88, -89, -92, -93, -94, -95, -96, -99, -100, -104, -107, -110, -112, -113, -115, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -8, -9, -10, -11, -14, -16, -17, -19, -23, -25, -27, -29, -31, -33, -34, -37, -39, -41, -43, -45, -47, -49, -50, -54, -55, -57]) (l₂ := [-58, -63, -65, -66, -68, -69, -72, -74, -76, -77, -79, -81, -85, -88, -89, -92, -93, -94, -95, -96, -99, -100, -104, -107, -110, -112, -113, -115, -118, -120])
  have hm := merge_two (literal (valuationOf q) (927)) (literal (valuationOf q) (1071)) (literal (valuationOf q) (1096)) (countLit q [-1, -4, -7, -8, -9, -10, -11, -14, -16, -17, -19, -23, -25, -27, -29, -31, -33, -34, -37, -39, -41, -43, -45, -47, -49, -50, -54, -55, -57]) (countLit q [-58, -63, -65, -66, -68, -69, -72, -74, -76, -77, -79, -81, -85, -88, -89, -92, -93, -94, -95, -96, -99, -100, -104, -107, -110, -112, -113, -115, -118, -120]) (count1078 q) 6 13 (meaning927 q) (meaning1071 q) (meaning1096 q) hs
  change valuationOf q 927 = false ∨ valuationOf q 1071 = false ∨ valuationOf q 1096 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 927 = false ∨ valuation q 1071 = false ∨ valuation q 1096 = true := counterClause1096 (baseVal q)

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1096 = false := by
  rw [value1096]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1078 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1441)) (countLit q [-3]) (countLit q [-5]) (count1441 q) 1 (meaningNeg5 q) (meaning1441 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1441 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1441)) (countLit q [-3]) (countLit q [-5]) (count1441 q) 1 (meaningNeg3 q) (meaning1441 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1441 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1442)) (countLit q [-3]) (countLit q [-5]) (count1441 q) 1 1 (meaningNeg3 q) (meaningNeg5 q) (meaning1442 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 5 = true ∨ valuation q 1442 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1441)) (literal (valuationOf q) (1443)) (countLit q [-2]) (countLit q [-3, -5]) (count1443 q) 1 (meaning1441 q) (meaning1443 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1443 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1442)) (literal (valuationOf q) (1444)) (countLit q [-2]) (countLit q [-3, -5]) (count1443 q) 2 (meaning1442 q) (meaning1444 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1444 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1443)) (countLit q [-2]) (countLit q [-3, -5]) (count1443 q) 1 (meaningNeg2 q) (meaning1443 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1443 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1441 = false ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1444)) (countLit q [-2]) (countLit q [-3, -5]) (count1443 q) 1 1 (meaningNeg2 q) (meaning1441 q) (meaning1444 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1441 = false ∨ valuation q 1444 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1442 = false ∨ valuationOf q 1445 = true := by
  have hs : count1443 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1445)) (countLit q [-2]) (countLit q [-3, -5]) (count1443 q) 1 2 (meaningNeg2 q) (meaning1442 q) (meaning1445 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1442 = false ∨ valuation q 1445 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-6]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1446)) (countLit q [-6]) (countLit q [-12]) (count1446 q) 1 (meaningNeg12 q) (meaning1446 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1446 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-6]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1446)) (countLit q [-6]) (countLit q [-12]) (count1446 q) 1 (meaningNeg6 q) (meaning1446 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1446 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 12 = true ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-6]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (1447)) (countLit q [-6]) (countLit q [-12]) (count1446 q) 1 1 (meaningNeg6 q) (meaningNeg12 q) (meaning1447 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 12 = true ∨ valuation q 1447 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_right (literal (valuationOf q) (-15)) (literal (valuationOf q) (1448)) (countLit q [-13]) (countLit q [-15]) (count1448 q) 1 (meaningNeg15 q) (meaning1448 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1448 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1448)) (countLit q [-13]) (countLit q [-15]) (count1448 q) 1 (meaningNeg13 q) (meaning1448 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1448 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 15 = true ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (1449)) (countLit q [-13]) (countLit q [-15]) (count1448 q) 1 1 (meaningNeg13 q) (meaningNeg15 q) (meaning1449 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 15 = true ∨ valuation q 1449 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-6, -12]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-6, -12]) (l₂ := [-13, -15])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1450)) (countLit q [-6, -12]) (countLit q [-13, -15]) (count1450 q) 1 (meaning1448 q) (meaning1450 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1450 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-6, -12]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-6, -12]) (l₂ := [-13, -15])
  have hm := merge_right (literal (valuationOf q) (1449)) (literal (valuationOf q) (1451)) (countLit q [-6, -12]) (countLit q [-13, -15]) (count1450 q) 2 (meaning1449 q) (meaning1451 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1451 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-6, -12]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-6, -12]) (l₂ := [-13, -15])
  have hm := merge_left (literal (valuationOf q) (1446)) (literal (valuationOf q) (1450)) (countLit q [-6, -12]) (countLit q [-13, -15]) (count1450 q) 1 (meaning1446 q) (meaning1450 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1450 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-6, -12]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-6, -12]) (l₂ := [-13, -15])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1451)) (countLit q [-6, -12]) (countLit q [-13, -15]) (count1450 q) 1 1 (meaning1446 q) (meaning1448 q) (meaning1451 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1448 = false ∨ valuation q 1451 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1452 = true := by
  have hs : count1450 q = (countLit q [-6, -12]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-6, -12]) (l₂ := [-13, -15])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1452)) (countLit q [-6, -12]) (countLit q [-13, -15]) (count1450 q) 1 2 (meaning1446 q) (meaning1449 q) (meaning1452 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1449 = false ∨ valuation q 1452 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-6, -12]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-6, -12]) (l₂ := [-13, -15])
  have hm := merge_left (literal (valuationOf q) (1447)) (literal (valuationOf q) (1451)) (countLit q [-6, -12]) (countLit q [-13, -15]) (count1450 q) 2 (meaning1447 q) (meaning1451 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1451 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1452 = true := by
  have hs : count1450 q = (countLit q [-6, -12]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-6, -12]) (l₂ := [-13, -15])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1452)) (countLit q [-6, -12]) (countLit q [-13, -15]) (count1450 q) 2 1 (meaning1447 q) (meaning1448 q) (meaning1452 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1448 = false ∨ valuation q 1452 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1453 = true := by
  have hs : count1450 q = (countLit q [-6, -12]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-6, -12]) (l₂ := [-13, -15])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1453)) (countLit q [-6, -12]) (countLit q [-13, -15]) (count1450 q) 2 2 (meaning1447 q) (meaning1449 q) (meaning1453 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1449 = false ∨ valuation q 1453 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1450)) (literal (valuationOf q) (1454)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1454 q) 1 (meaning1450 q) (meaning1454 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1454 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E004.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112004
