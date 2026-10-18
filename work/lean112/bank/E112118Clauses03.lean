import E112118Semantics
import B112E118Inputs
namespace Snake9.Regrowth.E112118
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause97 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1273 = true := by
  have hs : count1272 q = (countLit q [-74]) + (countLit q [-75, -79]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -79])
  have hm := merge_right (literal (valuationOf q) (1271)) (literal (valuationOf q) (1273)) (countLit q [-74]) (countLit q [-75, -79]) (count1272 q) 2 (meaning1271 q) (meaning1273 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1273 = true := counterClause97 (baseVal q)

theorem counterClause98 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1272 = true := by
  have hs : count1272 q = (countLit q [-74]) + (countLit q [-75, -79]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -79])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1272)) (countLit q [-74]) (countLit q [-75, -79]) (count1272 q) 1 (meaningNeg74 q) (meaning1272 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1272 = true := counterClause98 (baseVal q)

theorem counterClause99 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1270 = false ∨ valuationOf q 1273 = true := by
  have hs : count1272 q = (countLit q [-74]) + (countLit q [-75, -79]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -79])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (1270)) (literal (valuationOf q) (1273)) (countLit q [-74]) (countLit q [-75, -79]) (count1272 q) 1 1 (meaningNeg74 q) (meaning1270 q) (meaning1273 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1270 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1270 = false ∨ valuation q 1273 = true := counterClause99 (baseVal q)

theorem counterClause100 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1275 = true := by
  have hs : count1275 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1275)) (countLit q [-84]) (countLit q [-86]) (count1275 q) 1 (meaningNeg86 q) (meaning1275 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1275 = true := counterClause100 (baseVal q)

theorem counterClause101 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-81]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-84, -86])
  have hm := merge_right (literal (valuationOf q) (1275)) (literal (valuationOf q) (1277)) (countLit q [-81]) (countLit q [-84, -86]) (count1277 q) 1 (meaning1275 q) (meaning1277 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1277 = true := counterClause101 (baseVal q)

theorem counterClause102 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-81]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-84, -86])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1277)) (countLit q [-81]) (countLit q [-84, -86]) (count1277 q) 1 (meaningNeg81 q) (meaning1277 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1277 = true := counterClause102 (baseVal q)

theorem counterClause103 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1280 = true := by
  have hs : count1280 q = (countLit q [-74, -75, -79]) + (countLit q [-81, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -79]) (l₂ := [-81, -84, -86])
  have hm := merge_right (literal (valuationOf q) (1277)) (literal (valuationOf q) (1280)) (countLit q [-74, -75, -79]) (countLit q [-81, -84, -86]) (count1280 q) 1 (meaning1277 q) (meaning1280 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1280 = true := counterClause103 (baseVal q)

theorem counterClause104 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1280 = true := by
  have hs : count1280 q = (countLit q [-74, -75, -79]) + (countLit q [-81, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -79]) (l₂ := [-81, -84, -86])
  have hm := merge_left (literal (valuationOf q) (1272)) (literal (valuationOf q) (1280)) (countLit q [-74, -75, -79]) (countLit q [-81, -84, -86]) (count1280 q) 1 (meaning1272 q) (meaning1280 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1280 = true := counterClause104 (baseVal q)

theorem counterClause105 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1281 = true := by
  have hs : count1280 q = (countLit q [-74, -75, -79]) + (countLit q [-81, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -79]) (l₂ := [-81, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1277)) (literal (valuationOf q) (1281)) (countLit q [-74, -75, -79]) (countLit q [-81, -84, -86]) (count1280 q) 1 1 (meaning1272 q) (meaning1277 q) (meaning1281 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1277 = false ∨ valuation q 1281 = true := counterClause105 (baseVal q)

theorem counterClause106 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1281 = true := by
  have hs : count1280 q = (countLit q [-74, -75, -79]) + (countLit q [-81, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -79]) (l₂ := [-81, -84, -86])
  have hm := merge_left (literal (valuationOf q) (1273)) (literal (valuationOf q) (1281)) (countLit q [-74, -75, -79]) (countLit q [-81, -84, -86]) (count1280 q) 2 (meaning1273 q) (meaning1281 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1281 = true := counterClause106 (baseVal q)

theorem counterClause107 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-87]) + (countLit q [-89, -93]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89, -93])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1288)) (countLit q [-87]) (countLit q [-89, -93]) (count1288 q) 1 (meaningNeg87 q) (meaning1288 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1288 = true := counterClause107 (baseVal q)

theorem counterClause108 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1291 = true := by
  have hs : count1291 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1291)) (countLit q [-95]) (countLit q [-96]) (count1291 q) 1 (meaningNeg96 q) (meaning1291 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1291 = true := counterClause108 (baseVal q)

theorem counterClause109 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1291 = true := by
  have hs : count1291 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1291)) (countLit q [-95]) (countLit q [-96]) (count1291 q) 1 (meaningNeg95 q) (meaning1291 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1291 = true := counterClause109 (baseVal q)

theorem counterClause110 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-94]) + (countLit q [-95, -96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95, -96])
  have hm := merge_right (literal (valuationOf q) (1291)) (literal (valuationOf q) (1293)) (countLit q [-94]) (countLit q [-95, -96]) (count1293 q) 1 (meaning1291 q) (meaning1293 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1293 = true := counterClause110 (baseVal q)

theorem counterClause111 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-94]) + (countLit q [-95, -96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95, -96])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1293)) (countLit q [-94]) (countLit q [-95, -96]) (count1293 q) 1 (meaningNeg94 q) (meaning1293 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1293 = true := counterClause111 (baseVal q)

theorem counterClause112 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1296 = true := by
  have hs : count1296 q = (countLit q [-87, -89, -93]) + (countLit q [-94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -93]) (l₂ := [-94, -95, -96])
  have hm := merge_right (literal (valuationOf q) (1293)) (literal (valuationOf q) (1296)) (countLit q [-87, -89, -93]) (countLit q [-94, -95, -96]) (count1296 q) 1 (meaning1293 q) (meaning1296 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1296 = true := counterClause112 (baseVal q)

theorem counterClause113 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1293 = false ∨ valuationOf q 1297 = true := by
  have hs : count1296 q = (countLit q [-87, -89, -93]) + (countLit q [-94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -93]) (l₂ := [-94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1288)) (literal (valuationOf q) (1293)) (literal (valuationOf q) (1297)) (countLit q [-87, -89, -93]) (countLit q [-94, -95, -96]) (count1296 q) 1 1 (meaning1288 q) (meaning1293 q) (meaning1297 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1293 = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1293 = false ∨ valuation q 1297 = true := counterClause113 (baseVal q)

theorem counterClause114 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1302 = true := by
  have hs : count1302 q = (countLit q [-74, -75, -79, -81, -84, -86]) + (countLit q [-87, -89, -93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -79, -81, -84, -86]) (l₂ := [-87, -89, -93, -94, -95, -96])
  have hm := merge_right (literal (valuationOf q) (1296)) (literal (valuationOf q) (1302)) (countLit q [-74, -75, -79, -81, -84, -86]) (countLit q [-87, -89, -93, -94, -95, -96]) (count1302 q) 1 (meaning1296 q) (meaning1302 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1302 = true := counterClause114 (baseVal q)

theorem counterClause115 (q : Nat → Bool) : valuationOf q 1297 = false ∨ valuationOf q 1303 = true := by
  have hs : count1302 q = (countLit q [-74, -75, -79, -81, -84, -86]) + (countLit q [-87, -89, -93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -79, -81, -84, -86]) (l₂ := [-87, -89, -93, -94, -95, -96])
  have hm := merge_right (literal (valuationOf q) (1297)) (literal (valuationOf q) (1303)) (countLit q [-74, -75, -79, -81, -84, -86]) (countLit q [-87, -89, -93, -94, -95, -96]) (count1302 q) 2 (meaning1297 q) (meaning1303 q) hs
  change valuationOf q 1297 = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 1297 = false ∨ valuation q 1303 = true := counterClause115 (baseVal q)

theorem counterClause116 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1303 = true := by
  have hs : count1302 q = (countLit q [-74, -75, -79, -81, -84, -86]) + (countLit q [-87, -89, -93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -79, -81, -84, -86]) (l₂ := [-87, -89, -93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1280)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1303)) (countLit q [-74, -75, -79, -81, -84, -86]) (countLit q [-87, -89, -93, -94, -95, -96]) (count1302 q) 1 1 (meaning1280 q) (meaning1296 q) (meaning1303 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1296 = false ∨ valuation q 1303 = true := counterClause116 (baseVal q)

theorem counterClause117 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1304 = true := by
  have hs : count1302 q = (countLit q [-74, -75, -79, -81, -84, -86]) + (countLit q [-87, -89, -93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -79, -81, -84, -86]) (l₂ := [-87, -89, -93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1280)) (literal (valuationOf q) (1297)) (literal (valuationOf q) (1304)) (countLit q [-74, -75, -79, -81, -84, -86]) (countLit q [-87, -89, -93, -94, -95, -96]) (count1302 q) 1 2 (meaning1280 q) (meaning1297 q) (meaning1304 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1297 = false ∨ valuation q 1304 = true := counterClause117 (baseVal q)

theorem counterClause118 (q : Nat → Bool) : valuationOf q 1281 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1304 = true := by
  have hs : count1302 q = (countLit q [-74, -75, -79, -81, -84, -86]) + (countLit q [-87, -89, -93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -79, -81, -84, -86]) (l₂ := [-87, -89, -93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1281)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1304)) (countLit q [-74, -75, -79, -81, -84, -86]) (countLit q [-87, -89, -93, -94, -95, -96]) (count1302 q) 2 1 (meaning1281 q) (meaning1296 q) (meaning1304 q) hs
  change valuationOf q 1281 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 1281 = false ∨ valuation q 1296 = false ∨ valuation q 1304 = true := counterClause118 (baseVal q)

theorem counterClause119 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1313 = true := by
  have hs : count1309 q = (countLit q [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73]) + (countLit q [-74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73]) (l₂ := [-74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1264)) (literal (valuationOf q) (1304)) (literal (valuationOf q) (1313)) (countLit q [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73]) (countLit q [-74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]) (count1309 q) 2 3 (meaning1264 q) (meaning1304 q) (meaning1313 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1304 = false ∨ valuation q 1313 = true := counterClause119 (baseVal q)

theorem counterClause120 (q : Nat → Bool) : valuationOf q 1265 = false ∨ valuationOf q 1303 = false ∨ valuationOf q 1313 = true := by
  have hs : count1309 q = (countLit q [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73]) + (countLit q [-74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73]) (l₂ := [-74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1265)) (literal (valuationOf q) (1303)) (literal (valuationOf q) (1313)) (countLit q [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73]) (countLit q [-74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]) (count1309 q) 3 2 (meaning1265 q) (meaning1303 q) (meaning1313 q) hs
  change valuationOf q 1265 = false ∨ valuationOf q 1303 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 1265 = false ∨ valuation q 1303 = false ∨ valuation q 1313 = true := counterClause120 (baseVal q)

theorem counterClause121 (q : Nat → Bool) : valuationOf q 1265 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1314 = true := by
  have hs : count1309 q = (countLit q [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73]) + (countLit q [-74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73]) (l₂ := [-74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1265)) (literal (valuationOf q) (1304)) (literal (valuationOf q) (1314)) (countLit q [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73]) (countLit q [-74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]) (count1309 q) 3 3 (meaning1265 q) (meaning1304 q) (meaning1314 q) hs
  change valuationOf q 1265 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 1265 = false ∨ valuation q 1304 = false ∨ valuation q 1314 = true := counterClause121 (baseVal q)

theorem counterClause122 (q : Nat → Bool) : valuationOf q 1266 = false ∨ valuationOf q 1302 = false ∨ valuationOf q 1313 = true := by
  have hs : count1309 q = (countLit q [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73]) + (countLit q [-74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73]) (l₂ := [-74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1266)) (literal (valuationOf q) (1302)) (literal (valuationOf q) (1313)) (countLit q [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73]) (countLit q [-74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]) (count1309 q) 4 1 (meaning1266 q) (meaning1302 q) (meaning1313 q) hs
  change valuationOf q 1266 = false ∨ valuationOf q 1302 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 1266 = false ∨ valuation q 1302 = false ∨ valuation q 1313 = true := counterClause122 (baseVal q)

theorem counterClause123 (q : Nat → Bool) : valuationOf q 1224 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1322 = true := by
  have hs : count1316 q = (countLit q [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25, -26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]) + (countLit q [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73, -74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25, -26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]) (l₂ := [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73, -74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1224)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1322)) (countLit q [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25, -26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]) (countLit q [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73, -74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]) (count1316 q) 1 6 (meaning1224 q) (meaning1314 q) (meaning1322 q) hs
  change valuationOf q 1224 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 1224 = false ∨ valuation q 1314 = false ∨ valuation q 1322 = true := counterClause123 (baseVal q)

theorem counterClause124 (q : Nat → Bool) : valuationOf q 1225 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1322 = true := by
  have hs : count1316 q = (countLit q [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25, -26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]) + (countLit q [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73, -74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25, -26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]) (l₂ := [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73, -74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1225)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1322)) (countLit q [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25, -26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]) (countLit q [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73, -74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]) (count1316 q) 2 5 (meaning1225 q) (meaning1313 q) (meaning1322 q) hs
  change valuationOf q 1225 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 1225 = false ∨ valuation q 1313 = false ∨ valuation q 1322 = true := counterClause124 (baseVal q)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false := by
  rw [value1322]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1316 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem block3 (q : Snake 81) (h : Conditions q) : B112E118.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h⟩

end
end Snake9.Regrowth.E112118
