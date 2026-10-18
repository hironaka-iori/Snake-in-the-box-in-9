import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 1021 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1104 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1021)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1104)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 6 4 (meaning1021 q) (meaning1082 q) (meaning1104 q) hs
  change valuationOf q 1021 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 1021 = false ∨ valuation q 1082 = false ∨ valuation q 1104 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 1021 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1105 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1021)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1105)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 6 5 (meaning1021 q) (meaning1083 q) (meaning1105 q) hs
  change valuationOf q 1021 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 1021 = false ∨ valuation q 1083 = false ∨ valuation q 1105 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 1021 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1106 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1021)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1106)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 6 6 (meaning1021 q) (meaning1084 q) (meaning1106 q) hs
  change valuationOf q 1021 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 1021 = false ∨ valuation q 1084 = false ∨ valuation q 1106 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 1021 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1107 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1021)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1107)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 6 7 (meaning1021 q) (meaning1085 q) (meaning1107 q) hs
  change valuationOf q 1021 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1107 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1021 = false ∨ valuation q 1085 = false ∨ valuation q 1107 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1021 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1108 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1021)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1108)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 6 8 (meaning1021 q) (meaning1086 q) (meaning1108 q) hs
  change valuationOf q 1021 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1108 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1021 = false ∨ valuation q 1086 = false ∨ valuation q 1108 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 1022 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1104 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1022)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1104)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 7 3 (meaning1022 q) (meaning1081 q) (meaning1104 q) hs
  change valuationOf q 1022 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1022 = false ∨ valuation q 1081 = false ∨ valuation q 1104 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 1022 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1105 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1022)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1105)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 7 4 (meaning1022 q) (meaning1082 q) (meaning1105 q) hs
  change valuationOf q 1022 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1022 = false ∨ valuation q 1082 = false ∨ valuation q 1105 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 1022 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1106 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1022)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1106)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 7 5 (meaning1022 q) (meaning1083 q) (meaning1106 q) hs
  change valuationOf q 1022 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1022 = false ∨ valuation q 1083 = false ∨ valuation q 1106 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 1022 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1107 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1022)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1107)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 7 6 (meaning1022 q) (meaning1084 q) (meaning1107 q) hs
  change valuationOf q 1022 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1107 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1022 = false ∨ valuation q 1084 = false ∨ valuation q 1107 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 1023 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1105 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1023)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1105)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 8 3 (meaning1023 q) (meaning1081 q) (meaning1105 q) hs
  change valuationOf q 1023 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1023 = false ∨ valuation q 1081 = false ∨ valuation q 1105 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1023 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1106 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1023)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1106)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 8 4 (meaning1023 q) (meaning1082 q) (meaning1106 q) hs
  change valuationOf q 1023 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1023 = false ∨ valuation q 1082 = false ∨ valuation q 1106 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 1023 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1107 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1023)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1107)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 8 5 (meaning1023 q) (meaning1083 q) (meaning1107 q) hs
  change valuationOf q 1023 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1107 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1023 = false ∨ valuation q 1083 = false ∨ valuation q 1107 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1106 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1024)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1106)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 9 3 (meaning1024 q) (meaning1081 q) (meaning1106 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1081 = false ∨ valuation q 1106 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1107 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1024)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1107)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 9 4 (meaning1024 q) (meaning1082 q) (meaning1107 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1107 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1082 = false ∨ valuation q 1107 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 956 = false ∨ valuationOf q 1109 = false ∨ valuationOf q 1136 = true := by
  have hs : count1116 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (956)) (literal (valuationOf q) (1109)) (literal (valuationOf q) (1136)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1116 q) 6 15 (meaning956 q) (meaning1109 q) (meaning1136 q) hs
  change valuationOf q 956 = false ∨ valuationOf q 1109 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 956 = false ∨ valuation q 1109 = false ∨ valuation q 1136 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 1108 = false ∨ valuationOf q 1136 = true := by
  have hs : count1116 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (957)) (literal (valuationOf q) (1108)) (literal (valuationOf q) (1136)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1116 q) 7 14 (meaning957 q) (meaning1108 q) (meaning1136 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 1108 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 1108 = false ∨ valuation q 1136 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 1107 = false ∨ valuationOf q 1136 = true := by
  have hs : count1116 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (958)) (literal (valuationOf q) (1107)) (literal (valuationOf q) (1136)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1116 q) 8 13 (meaning958 q) (meaning1107 q) (meaning1136 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 1107 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 1107 = false ∨ valuation q 1136 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 1106 = false ∨ valuationOf q 1136 = true := by
  have hs : count1116 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (1106)) (literal (valuationOf q) (1136)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1116 q) 9 12 (meaning959 q) (meaning1106 q) (meaning1136 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 1106 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 1106 = false ∨ valuation q 1136 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1136 = true := by
  have hs : count1116 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (1105)) (literal (valuationOf q) (1136)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1116 q) 10 11 (meaning960 q) (meaning1105 q) (meaning1136 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 1105 = false ∨ valuation q 1136 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1136 = true := by
  have hs : count1116 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (961)) (literal (valuationOf q) (1104)) (literal (valuationOf q) (1136)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1116 q) 11 10 (meaning961 q) (meaning1104 q) (meaning1136 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 1104 = false ∨ valuation q 1136 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1136 = true := by
  have hs : count1116 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (962)) (literal (valuationOf q) (1103)) (literal (valuationOf q) (1136)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1116 q) 12 9 (meaning962 q) (meaning1103 q) (meaning1136 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 1103 = false ∨ valuation q 1136 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1136 = true := by
  have hs : count1116 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (963)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1136)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1116 q) 13 8 (meaning963 q) (meaning1102 q) (meaning1136 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 1102 = false ∨ valuation q 1136 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 964 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1136 = true := by
  have hs : count1116 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (964)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1136)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1116 q) 14 7 (meaning964 q) (meaning1101 q) (meaning1136 q) hs
  change valuationOf q 964 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 964 = false ∨ valuation q 1101 = false ∨ valuation q 1136 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 965 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1136 = true := by
  have hs : count1116 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (965)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1136)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1116 q) 15 6 (meaning965 q) (meaning1100 q) (meaning1136 q) hs
  change valuationOf q 965 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 965 = false ∨ valuation q 1100 = false ∨ valuation q 1136 = true := counterClause1464 (baseVal q)

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 1136 = false := by
  rw [value1136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1116 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1492)) (countLit q [-11]) (countLit q [-12]) (count1492 q) 1 (meaningNeg12 q) (meaning1492 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1492 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-11, -12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-11, -12]) (l₂ := [-14, -15])
  have hm := merge_left (literal (valuationOf q) (1492)) (literal (valuationOf q) (1496)) (countLit q [-11, -12]) (countLit q [-14, -15]) (count1496 q) 1 (meaning1492 q) (meaning1496 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1496 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-2, -5, -9]) + (countLit q [-11, -12, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -9]) (l₂ := [-11, -12, -14, -15])
  have hm := merge_right (literal (valuationOf q) (1496)) (literal (valuationOf q) (1500)) (countLit q [-2, -5, -9]) (countLit q [-11, -12, -14, -15]) (count1500 q) 1 (meaning1496 q) (meaning1500 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1500 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-16]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1507)) (countLit q [-16]) (countLit q [-17]) (count1507 q) 1 (meaningNeg17 q) (meaning1507 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1507 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1509 = true := by
  have hs : count1509 q = (countLit q [-19]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1509)) (countLit q [-19]) (countLit q [-23]) (count1509 q) 1 (meaningNeg19 q) (meaning1509 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1509 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1511 = true := by
  have hs : count1511 q = (countLit q [-16, -17]) + (countLit q [-19, -23]) := List.countP_append (p := literal q) (l₁ := [-16, -17]) (l₂ := [-19, -23])
  have hm := merge_left (literal (valuationOf q) (1507)) (literal (valuationOf q) (1511)) (countLit q [-16, -17]) (countLit q [-19, -23]) (count1511 q) 1 (meaning1507 q) (meaning1511 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1511 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1512 = true := by
  have hs : count1511 q = (countLit q [-16, -17]) + (countLit q [-19, -23]) := List.countP_append (p := literal q) (l₁ := [-16, -17]) (l₂ := [-19, -23])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1512)) (countLit q [-16, -17]) (countLit q [-19, -23]) (count1511 q) 1 1 (meaning1507 q) (meaning1509 q) (meaning1512 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1509 = false ∨ valuation q 1512 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E097.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112097
