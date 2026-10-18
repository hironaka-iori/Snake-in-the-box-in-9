import E112149Semantics
import B112E149Inputs
namespace Snake9.Regrowth.E112149
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 1250 = false ∨ valuationOf q 1272 = true := by
  have hs : count1272 q = (countLit q [-49, -50, -52, -54, -56, -58]) + (countLit q [-61, -62, -64, -66, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-49, -50, -52, -54, -56, -58]) (l₂ := [-61, -62, -64, -66, -68, -71])
  have hm := merge_left (literal (valuationOf q) (1250)) (literal (valuationOf q) (1272)) (countLit q [-49, -50, -52, -54, -56, -58]) (countLit q [-61, -62, -64, -66, -68, -71]) (count1272 q) 1 (meaning1250 q) (meaning1272 q) hs
  change valuationOf q 1250 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 1250 = false ∨ valuation q 1272 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1281 = true := by
  have hs : count1281 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1281)) (countLit q [-76]) (countLit q [-79]) (count1281 q) 1 (meaningNeg76 q) (meaning1281 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1281 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 1281 = false ∨ valuationOf q 1283 = true := by
  have hs : count1283 q = (countLit q [-74]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76, -79])
  have hm := merge_right (literal (valuationOf q) (1281)) (literal (valuationOf q) (1283)) (countLit q [-74]) (countLit q [-76, -79]) (count1283 q) 1 (meaning1281 q) (meaning1283 q) hs
  change valuationOf q 1281 = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 1281 = false ∨ valuation q 1283 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1283 = true := by
  have hs : count1283 q = (countLit q [-74]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76, -79])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1283)) (countLit q [-74]) (countLit q [-76, -79]) (count1283 q) 1 (meaningNeg74 q) (meaning1283 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1283 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1281 = false ∨ valuationOf q 1284 = true := by
  have hs : count1283 q = (countLit q [-74]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76, -79])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (1281)) (literal (valuationOf q) (1284)) (countLit q [-74]) (countLit q [-76, -79]) (count1283 q) 1 1 (meaningNeg74 q) (meaning1281 q) (meaning1284 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1281 = false ∨ valuation q 1284 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1286 = true := by
  have hs : count1286 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_right (literal (valuationOf q) (-83)) (literal (valuationOf q) (1286)) (countLit q [-81]) (countLit q [-83]) (count1286 q) 1 (meaningNeg83 q) (meaning1286 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1286 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1286 = true := by
  have hs : count1286 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1286)) (countLit q [-81]) (countLit q [-83]) (count1286 q) 1 (meaningNeg81 q) (meaning1286 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1286 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 1286 = false ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-80]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81, -83])
  have hm := merge_right (literal (valuationOf q) (1286)) (literal (valuationOf q) (1288)) (countLit q [-80]) (countLit q [-81, -83]) (count1288 q) 1 (meaning1286 q) (meaning1288 q) hs
  change valuationOf q 1286 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 1286 = false ∨ valuation q 1288 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-80]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81, -83])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1288)) (countLit q [-80]) (countLit q [-81, -83]) (count1288 q) 1 (meaningNeg80 q) (meaning1288 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1288 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1291 = true := by
  have hs : count1291 q = (countLit q [-74, -76, -79]) + (countLit q [-80, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79]) (l₂ := [-80, -81, -83])
  have hm := merge_right (literal (valuationOf q) (1288)) (literal (valuationOf q) (1291)) (countLit q [-74, -76, -79]) (countLit q [-80, -81, -83]) (count1291 q) 1 (meaning1288 q) (meaning1291 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1291 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 1283 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1292 = true := by
  have hs : count1291 q = (countLit q [-74, -76, -79]) + (countLit q [-80, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79]) (l₂ := [-80, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1283)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1292)) (countLit q [-74, -76, -79]) (countLit q [-80, -81, -83]) (count1291 q) 1 1 (meaning1283 q) (meaning1288 q) (meaning1292 q) hs
  change valuationOf q 1283 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 1283 = false ∨ valuation q 1288 = false ∨ valuation q 1292 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 1284 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1293 = true := by
  have hs : count1291 q = (countLit q [-74, -76, -79]) + (countLit q [-80, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79]) (l₂ := [-80, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1284)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1293)) (countLit q [-74, -76, -79]) (countLit q [-80, -81, -83]) (count1291 q) 2 1 (meaning1284 q) (meaning1288 q) (meaning1293 q) hs
  change valuationOf q 1284 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 1284 = false ∨ valuation q 1288 = false ∨ valuation q 1293 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1297 = true := by
  have hs : count1297 q = (countLit q [-88]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1297)) (countLit q [-88]) (countLit q [-89]) (count1297 q) 1 (meaningNeg89 q) (meaning1297 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1297 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 1297 = false ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-86]) + (countLit q [-88, -89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -89])
  have hm := merge_right (literal (valuationOf q) (1297)) (literal (valuationOf q) (1299)) (countLit q [-86]) (countLit q [-88, -89]) (count1299 q) 1 (meaning1297 q) (meaning1299 q) hs
  change valuationOf q 1297 = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 1297 = false ∨ valuation q 1299 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-86]) + (countLit q [-88, -89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -89])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1299)) (countLit q [-86]) (countLit q [-88, -89]) (count1299 q) 1 (meaningNeg86 q) (meaning1299 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1299 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1302 = true := by
  have hs : count1302 q = (countLit q [-92]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1302)) (countLit q [-92]) (countLit q [-94]) (count1302 q) 1 (meaningNeg92 q) (meaning1302 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1302 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-92, -94]) + (countLit q [-96, -98]) := List.countP_append (p := literal q) (l₁ := [-92, -94]) (l₂ := [-96, -98])
  have hm := merge_left (literal (valuationOf q) (1302)) (literal (valuationOf q) (1306)) (countLit q [-92, -94]) (countLit q [-96, -98]) (count1306 q) 1 (meaning1302 q) (meaning1306 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1306 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 1306 = false ∨ valuationOf q 1310 = true := by
  have hs : count1310 q = (countLit q [-86, -88, -89]) + (countLit q [-92, -94, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89]) (l₂ := [-92, -94, -96, -98])
  have hm := merge_right (literal (valuationOf q) (1306)) (literal (valuationOf q) (1310)) (countLit q [-86, -88, -89]) (countLit q [-92, -94, -96, -98]) (count1310 q) 1 (meaning1306 q) (meaning1310 q) hs
  change valuationOf q 1306 = false ∨ valuationOf q 1310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 1306 = false ∨ valuation q 1310 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 1299 = false ∨ valuationOf q 1310 = true := by
  have hs : count1310 q = (countLit q [-86, -88, -89]) + (countLit q [-92, -94, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89]) (l₂ := [-92, -94, -96, -98])
  have hm := merge_left (literal (valuationOf q) (1299)) (literal (valuationOf q) (1310)) (countLit q [-86, -88, -89]) (countLit q [-92, -94, -96, -98]) (count1310 q) 1 (meaning1299 q) (meaning1310 q) hs
  change valuationOf q 1299 = false ∨ valuationOf q 1310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 1299 = false ∨ valuation q 1310 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1310 = false ∨ valuationOf q 1318 = true := by
  have hs : count1317 q = (countLit q [-74, -76, -79, -80, -81, -83]) + (countLit q [-86, -88, -89, -92, -94, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80, -81, -83]) (l₂ := [-86, -88, -89, -92, -94, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1310)) (literal (valuationOf q) (1318)) (countLit q [-74, -76, -79, -80, -81, -83]) (countLit q [-86, -88, -89, -92, -94, -96, -98]) (count1317 q) 1 1 (meaning1291 q) (meaning1310 q) (meaning1318 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1310 = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1310 = false ∨ valuation q 1318 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1318 = true := by
  have hs : count1317 q = (countLit q [-74, -76, -79, -80, -81, -83]) + (countLit q [-86, -88, -89, -92, -94, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80, -81, -83]) (l₂ := [-86, -88, -89, -92, -94, -96, -98])
  have hm := merge_left (literal (valuationOf q) (1292)) (literal (valuationOf q) (1318)) (countLit q [-74, -76, -79, -80, -81, -83]) (countLit q [-86, -88, -89, -92, -94, -96, -98]) (count1317 q) 2 (meaning1292 q) (meaning1318 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1318 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1310 = false ∨ valuationOf q 1319 = true := by
  have hs : count1317 q = (countLit q [-74, -76, -79, -80, -81, -83]) + (countLit q [-86, -88, -89, -92, -94, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80, -81, -83]) (l₂ := [-86, -88, -89, -92, -94, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1292)) (literal (valuationOf q) (1310)) (literal (valuationOf q) (1319)) (countLit q [-74, -76, -79, -80, -81, -83]) (countLit q [-86, -88, -89, -92, -94, -96, -98]) (count1317 q) 2 1 (meaning1292 q) (meaning1310 q) (meaning1319 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1310 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1310 = false ∨ valuation q 1319 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1319 = true := by
  have hs : count1317 q = (countLit q [-74, -76, -79, -80, -81, -83]) + (countLit q [-86, -88, -89, -92, -94, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -80, -81, -83]) (l₂ := [-86, -88, -89, -92, -94, -96, -98])
  have hm := merge_left (literal (valuationOf q) (1293)) (literal (valuationOf q) (1319)) (countLit q [-74, -76, -79, -80, -81, -83]) (countLit q [-86, -88, -89, -92, -94, -96, -98]) (count1317 q) 3 (meaning1293 q) (meaning1319 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1319 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1328 = true := by
  have hs : count1326 q = (countLit q [-49, -50, -52, -54, -56, -58, -61, -62, -64, -66, -68, -71]) + (countLit q [-74, -76, -79, -80, -81, -83, -86, -88, -89, -92, -94, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-49, -50, -52, -54, -56, -58, -61, -62, -64, -66, -68, -71]) (l₂ := [-74, -76, -79, -80, -81, -83, -86, -88, -89, -92, -94, -96, -98])
  have hm := merge_right (literal (valuationOf q) (1319)) (literal (valuationOf q) (1328)) (countLit q [-49, -50, -52, -54, -56, -58, -61, -62, -64, -66, -68, -71]) (countLit q [-74, -76, -79, -80, -81, -83, -86, -88, -89, -92, -94, -96, -98]) (count1326 q) 3 (meaning1319 q) (meaning1328 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1328 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1328 = true := by
  have hs : count1326 q = (countLit q [-49, -50, -52, -54, -56, -58, -61, -62, -64, -66, -68, -71]) + (countLit q [-74, -76, -79, -80, -81, -83, -86, -88, -89, -92, -94, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-49, -50, -52, -54, -56, -58, -61, -62, -64, -66, -68, -71]) (l₂ := [-74, -76, -79, -80, -81, -83, -86, -88, -89, -92, -94, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1318)) (literal (valuationOf q) (1328)) (countLit q [-49, -50, -52, -54, -56, -58, -61, -62, -64, -66, -68, -71]) (countLit q [-74, -76, -79, -80, -81, -83, -86, -88, -89, -92, -94, -96, -98]) (count1326 q) 1 2 (meaning1272 q) (meaning1318 q) (meaning1328 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1318 = false ∨ valuation q 1328 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 1236 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1343 = true := by
  have hs : count1335 q = (countLit q [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23, -24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47]) + (countLit q [-49, -50, -52, -54, -56, -58, -61, -62, -64, -66, -68, -71, -74, -76, -79, -80, -81, -83, -86, -88, -89, -92, -94, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23, -24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47]) (l₂ := [-49, -50, -52, -54, -56, -58, -61, -62, -64, -66, -68, -71, -74, -76, -79, -80, -81, -83, -86, -88, -89, -92, -94, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1236)) (literal (valuationOf q) (1328)) (literal (valuationOf q) (1343)) (countLit q [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23, -24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47]) (countLit q [-49, -50, -52, -54, -56, -58, -61, -62, -64, -66, -68, -71, -74, -76, -79, -80, -81, -83, -86, -88, -89, -92, -94, -96, -98]) (count1335 q) 6 3 (meaning1236 q) (meaning1328 q) (meaning1343 q) hs
  change valuationOf q 1236 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 1236 = false ∨ valuation q 1328 = false ∨ valuation q 1343 = true := counterClause314 (baseVal q)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false := by
  rw [value1343]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1335 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 22 = false := by
  rw [value15, value17, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (164 : Vertex) (166 : Vertex) (172 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value23, value25, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (181 : Vertex) (183 : Vertex) (189 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E149.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h⟩

end
end Snake9.Regrowth.E112149
