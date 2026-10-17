import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1103)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 2 7 (meaning1017 q) (meaning1085 q) (meaning1103 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1085 = false ∨ valuation q 1103 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1104 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1104)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 2 8 (meaning1017 q) (meaning1086 q) (meaning1104 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1086 = false ∨ valuation q 1104 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1105 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1105)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 2 9 (meaning1017 q) (meaning1087 q) (meaning1105 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1087 = false ∨ valuation q 1105 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1106 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1106)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 2 10 (meaning1017 q) (meaning1088 q) (meaning1106 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1088 = false ∨ valuation q 1106 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1108 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1108)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 2 12 (meaning1017 q) (meaning1090 q) (meaning1108 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1108 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1090 = false ∨ valuation q 1108 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1018)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1100)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 3 3 (meaning1018 q) (meaning1081 q) (meaning1100 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1081 = false ∨ valuation q 1100 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1018)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1101)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 3 4 (meaning1018 q) (meaning1082 q) (meaning1101 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1082 = false ∨ valuation q 1101 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1018)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1102)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 3 5 (meaning1018 q) (meaning1083 q) (meaning1102 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1083 = false ∨ valuation q 1102 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1018)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1103)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 3 6 (meaning1018 q) (meaning1084 q) (meaning1103 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1084 = false ∨ valuation q 1103 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1104 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1018)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1104)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 3 7 (meaning1018 q) (meaning1085 q) (meaning1104 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1085 = false ∨ valuation q 1104 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1105 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1018)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1105)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 3 8 (meaning1018 q) (meaning1086 q) (meaning1105 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1086 = false ∨ valuation q 1105 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1106 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1018)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1106)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 3 9 (meaning1018 q) (meaning1087 q) (meaning1106 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1087 = false ∨ valuation q 1106 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1107 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1018)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1107)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 3 10 (meaning1018 q) (meaning1088 q) (meaning1107 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1107 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1088 = false ∨ valuation q 1107 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1108 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1018)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1108)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 3 11 (meaning1018 q) (meaning1089 q) (meaning1108 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1108 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1089 = false ∨ valuation q 1108 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1101)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 4 3 (meaning1019 q) (meaning1081 q) (meaning1101 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1081 = false ∨ valuation q 1101 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1102)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 4 4 (meaning1019 q) (meaning1082 q) (meaning1102 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1082 = false ∨ valuation q 1102 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1103)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 4 5 (meaning1019 q) (meaning1083 q) (meaning1103 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1083 = false ∨ valuation q 1103 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1104 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1104)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 4 6 (meaning1019 q) (meaning1084 q) (meaning1104 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1084 = false ∨ valuation q 1104 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1105 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1105)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 4 7 (meaning1019 q) (meaning1085 q) (meaning1105 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1085 = false ∨ valuation q 1105 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1106 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1106)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 4 8 (meaning1019 q) (meaning1086 q) (meaning1106 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1086 = false ∨ valuation q 1106 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1107 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1107)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 4 9 (meaning1019 q) (meaning1087 q) (meaning1107 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1107 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1087 = false ∨ valuation q 1107 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1108 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1108)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 4 10 (meaning1019 q) (meaning1088 q) (meaning1108 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1108 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1088 = false ∨ valuation q 1108 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1109 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1109)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 4 11 (meaning1019 q) (meaning1089 q) (meaning1109 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1109 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1089 = false ∨ valuation q 1109 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1080 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1080)) (literal (valuationOf q) (1101)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 5 2 (meaning1020 q) (meaning1080 q) (meaning1101 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1080 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1080 = false ∨ valuation q 1101 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1102)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 5 3 (meaning1020 q) (meaning1081 q) (meaning1102 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1081 = false ∨ valuation q 1102 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1103)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 5 4 (meaning1020 q) (meaning1082 q) (meaning1103 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1082 = false ∨ valuation q 1103 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1104 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1104)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 5 5 (meaning1020 q) (meaning1083 q) (meaning1104 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1083 = false ∨ valuation q 1104 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1105 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1105)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 5 6 (meaning1020 q) (meaning1084 q) (meaning1105 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1084 = false ∨ valuation q 1105 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1106 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1106)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 5 7 (meaning1020 q) (meaning1085 q) (meaning1106 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1085 = false ∨ valuation q 1106 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1107 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1107)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 5 8 (meaning1020 q) (meaning1086 q) (meaning1107 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1107 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1086 = false ∨ valuation q 1107 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1108 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1108)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 5 9 (meaning1020 q) (meaning1087 q) (meaning1108 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1108 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1087 = false ∨ valuation q 1108 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 1021 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1021)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1103)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 6 3 (meaning1021 q) (meaning1081 q) (meaning1103 q) hs
  change valuationOf q 1021 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1021 = false ∨ valuation q 1081 = false ∨ valuation q 1103 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E097.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112097
