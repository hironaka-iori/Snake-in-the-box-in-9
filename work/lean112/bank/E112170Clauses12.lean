import E112170Semantics
import B112E170Inputs
namespace Snake9.Regrowth.E112170
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 1282 = false ∨ valuationOf q 1284 = true := by
  have hs : count1283 q = (countLit q [-75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77, -79])
  have hm := merge_right (literal (valuationOf q) (1282)) (literal (valuationOf q) (1284)) (countLit q [-75]) (countLit q [-77, -79]) (count1283 q) 2 (meaning1282 q) (meaning1284 q) hs
  change valuationOf q 1282 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 1282 = false ∨ valuation q 1284 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1283 = true := by
  have hs : count1283 q = (countLit q [-75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77, -79])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1283)) (countLit q [-75]) (countLit q [-77, -79]) (count1283 q) 1 (meaningNeg75 q) (meaning1283 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1283 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1286 = true := by
  have hs : count1286 q = (countLit q [-82]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1286)) (countLit q [-82]) (countLit q [-85]) (count1286 q) 1 (meaningNeg85 q) (meaning1286 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1286 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1286 = true := by
  have hs : count1286 q = (countLit q [-82]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1286)) (countLit q [-82]) (countLit q [-85]) (count1286 q) 1 (meaningNeg82 q) (meaning1286 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1286 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 85 = true ∨ valuationOf q 1287 = true := by
  have hs : count1286 q = (countLit q [-82]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (1287)) (countLit q [-82]) (countLit q [-85]) (count1286 q) 1 1 (meaningNeg82 q) (meaningNeg85 q) (meaning1287 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 1287 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 1287 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 1286 = false ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-80]) + (countLit q [-82, -85]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82, -85])
  have hm := merge_right (literal (valuationOf q) (1286)) (literal (valuationOf q) (1288)) (countLit q [-80]) (countLit q [-82, -85]) (count1288 q) 1 (meaning1286 q) (meaning1288 q) hs
  change valuationOf q 1286 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 1286 = false ∨ valuation q 1288 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 1287 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-80]) + (countLit q [-82, -85]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82, -85])
  have hm := merge_right (literal (valuationOf q) (1287)) (literal (valuationOf q) (1289)) (countLit q [-80]) (countLit q [-82, -85]) (count1288 q) 2 (meaning1287 q) (meaning1289 q) hs
  change valuationOf q 1287 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 1287 = false ∨ valuation q 1289 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-80]) + (countLit q [-82, -85]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82, -85])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1288)) (countLit q [-80]) (countLit q [-82, -85]) (count1288 q) 1 (meaningNeg80 q) (meaning1288 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1288 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1291 = true := by
  have hs : count1291 q = (countLit q [-75, -77, -79]) + (countLit q [-80, -82, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -79]) (l₂ := [-80, -82, -85])
  have hm := merge_right (literal (valuationOf q) (1288)) (literal (valuationOf q) (1291)) (countLit q [-75, -77, -79]) (countLit q [-80, -82, -85]) (count1291 q) 1 (meaning1288 q) (meaning1291 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1291 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1292 = true := by
  have hs : count1291 q = (countLit q [-75, -77, -79]) + (countLit q [-80, -82, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -79]) (l₂ := [-80, -82, -85])
  have hm := merge_right (literal (valuationOf q) (1289)) (literal (valuationOf q) (1292)) (countLit q [-75, -77, -79]) (countLit q [-80, -82, -85]) (count1291 q) 2 (meaning1289 q) (meaning1292 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1292 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 1283 = false ∨ valuationOf q 1291 = true := by
  have hs : count1291 q = (countLit q [-75, -77, -79]) + (countLit q [-80, -82, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -79]) (l₂ := [-80, -82, -85])
  have hm := merge_left (literal (valuationOf q) (1283)) (literal (valuationOf q) (1291)) (countLit q [-75, -77, -79]) (countLit q [-80, -82, -85]) (count1291 q) 1 (meaning1283 q) (meaning1291 q) hs
  change valuationOf q 1283 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 1283 = false ∨ valuation q 1291 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 1283 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1292 = true := by
  have hs : count1291 q = (countLit q [-75, -77, -79]) + (countLit q [-80, -82, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -79]) (l₂ := [-80, -82, -85])
  have hm := merge_two (literal (valuationOf q) (1283)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1292)) (countLit q [-75, -77, -79]) (countLit q [-80, -82, -85]) (count1291 q) 1 1 (meaning1283 q) (meaning1288 q) (meaning1292 q) hs
  change valuationOf q 1283 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 1283 = false ∨ valuation q 1288 = false ∨ valuation q 1292 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 1283 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1293 = true := by
  have hs : count1291 q = (countLit q [-75, -77, -79]) + (countLit q [-80, -82, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -79]) (l₂ := [-80, -82, -85])
  have hm := merge_two (literal (valuationOf q) (1283)) (literal (valuationOf q) (1289)) (literal (valuationOf q) (1293)) (countLit q [-75, -77, -79]) (countLit q [-80, -82, -85]) (count1291 q) 1 2 (meaning1283 q) (meaning1289 q) (meaning1293 q) hs
  change valuationOf q 1283 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 1283 = false ∨ valuation q 1289 = false ∨ valuation q 1293 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 1284 = false ∨ valuationOf q 1292 = true := by
  have hs : count1291 q = (countLit q [-75, -77, -79]) + (countLit q [-80, -82, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -79]) (l₂ := [-80, -82, -85])
  have hm := merge_left (literal (valuationOf q) (1284)) (literal (valuationOf q) (1292)) (countLit q [-75, -77, -79]) (countLit q [-80, -82, -85]) (count1291 q) 2 (meaning1284 q) (meaning1292 q) hs
  change valuationOf q 1284 = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 1284 = false ∨ valuation q 1292 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1297 = true := by
  have hs : count1297 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1297)) (countLit q [-88]) (countLit q [-90]) (count1297 q) 1 (meaningNeg90 q) (meaning1297 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1297 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1297 = true := by
  have hs : count1297 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1297)) (countLit q [-88]) (countLit q [-90]) (count1297 q) 1 (meaningNeg88 q) (meaning1297 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1297 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 90 = true ∨ valuationOf q 1298 = true := by
  have hs : count1297 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (1298)) (countLit q [-88]) (countLit q [-90]) (count1297 q) 1 1 (meaningNeg88 q) (meaningNeg90 q) (meaning1298 q) hs
  change (! (valuationOf q 88)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 90 = true ∨ valuation q 1298 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 1297 = false ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-87]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88, -90])
  have hm := merge_right (literal (valuationOf q) (1297)) (literal (valuationOf q) (1299)) (countLit q [-87]) (countLit q [-88, -90]) (count1299 q) 1 (meaning1297 q) (meaning1299 q) hs
  change valuationOf q 1297 = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 1297 = false ∨ valuation q 1299 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 1298 = false ∨ valuationOf q 1300 = true := by
  have hs : count1299 q = (countLit q [-87]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88, -90])
  have hm := merge_right (literal (valuationOf q) (1298)) (literal (valuationOf q) (1300)) (countLit q [-87]) (countLit q [-88, -90]) (count1299 q) 2 (meaning1298 q) (meaning1300 q) hs
  change valuationOf q 1298 = false ∨ valuationOf q 1300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 1298 = false ∨ valuation q 1300 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-87]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88, -90])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1299)) (countLit q [-87]) (countLit q [-88, -90]) (count1299 q) 1 (meaningNeg87 q) (meaning1299 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1299 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1297 = false ∨ valuationOf q 1300 = true := by
  have hs : count1299 q = (countLit q [-87]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88, -90])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (1297)) (literal (valuationOf q) (1300)) (countLit q [-87]) (countLit q [-88, -90]) (count1299 q) 1 1 (meaningNeg87 q) (meaning1297 q) (meaning1300 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1300 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1297 = false ∨ valuation q 1300 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1302 = true := by
  have hs : count1302 q = (countLit q [-93]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-95])
  have hm := merge_right (literal (valuationOf q) (-95)) (literal (valuationOf q) (1302)) (countLit q [-93]) (countLit q [-95]) (count1302 q) 1 (meaningNeg95 q) (meaning1302 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1302 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1302 = true := by
  have hs : count1302 q = (countLit q [-93]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1302)) (countLit q [-93]) (countLit q [-95]) (count1302 q) 1 (meaningNeg93 q) (meaning1302 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1302 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 95 = true ∨ valuationOf q 1303 = true := by
  have hs : count1302 q = (countLit q [-93]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-95])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (-95)) (literal (valuationOf q) (1303)) (countLit q [-93]) (countLit q [-95]) (count1302 q) 1 1 (meaningNeg93 q) (meaningNeg95 q) (meaning1303 q) hs
  change (! (valuationOf q 93)) = false ∨ (! (valuationOf q 95)) = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 95 = true ∨ valuation q 1303 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1304 = true := by
  have hs : count1304 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1304)) (countLit q [-96]) (countLit q [-98]) (count1304 q) 1 (meaningNeg98 q) (meaning1304 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1304 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1304 = true := by
  have hs : count1304 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-96)) (literal (valuationOf q) (1304)) (countLit q [-96]) (countLit q [-98]) (count1304 q) 1 (meaningNeg96 q) (meaning1304 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1304 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 98 = true ∨ valuationOf q 1305 = true := by
  have hs : count1304 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (1305)) (countLit q [-96]) (countLit q [-98]) (count1304 q) 1 1 (meaningNeg96 q) (meaningNeg98 q) (meaning1305 q) hs
  change (! (valuationOf q 96)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 1305 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 98 = true ∨ valuation q 1305 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-93, -95]) + (countLit q [-96, -98]) := List.countP_append (p := literal q) (l₁ := [-93, -95]) (l₂ := [-96, -98])
  have hm := merge_right (literal (valuationOf q) (1304)) (literal (valuationOf q) (1306)) (countLit q [-93, -95]) (countLit q [-96, -98]) (count1306 q) 1 (meaning1304 q) (meaning1306 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1306 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 1305 = false ∨ valuationOf q 1307 = true := by
  have hs : count1306 q = (countLit q [-93, -95]) + (countLit q [-96, -98]) := List.countP_append (p := literal q) (l₁ := [-93, -95]) (l₂ := [-96, -98])
  have hm := merge_right (literal (valuationOf q) (1305)) (literal (valuationOf q) (1307)) (countLit q [-93, -95]) (countLit q [-96, -98]) (count1306 q) 2 (meaning1305 q) (meaning1307 q) hs
  change valuationOf q 1305 = false ∨ valuationOf q 1307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 1305 = false ∨ valuation q 1307 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-93, -95]) + (countLit q [-96, -98]) := List.countP_append (p := literal q) (l₁ := [-93, -95]) (l₂ := [-96, -98])
  have hm := merge_left (literal (valuationOf q) (1302)) (literal (valuationOf q) (1306)) (countLit q [-93, -95]) (countLit q [-96, -98]) (count1306 q) 1 (meaning1302 q) (meaning1306 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1306 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1307 = true := by
  have hs : count1306 q = (countLit q [-93, -95]) + (countLit q [-96, -98]) := List.countP_append (p := literal q) (l₁ := [-93, -95]) (l₂ := [-96, -98])
  have hm := merge_two (literal (valuationOf q) (1302)) (literal (valuationOf q) (1304)) (literal (valuationOf q) (1307)) (countLit q [-93, -95]) (countLit q [-96, -98]) (count1306 q) 1 1 (meaning1302 q) (meaning1304 q) (meaning1307 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1304 = false ∨ valuation q 1307 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 1303 = false ∨ valuationOf q 1307 = true := by
  have hs : count1306 q = (countLit q [-93, -95]) + (countLit q [-96, -98]) := List.countP_append (p := literal q) (l₁ := [-93, -95]) (l₂ := [-96, -98])
  have hm := merge_left (literal (valuationOf q) (1303)) (literal (valuationOf q) (1307)) (countLit q [-93, -95]) (countLit q [-96, -98]) (count1306 q) 2 (meaning1303 q) (meaning1307 q) hs
  change valuationOf q 1303 = false ∨ valuationOf q 1307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 1303 = false ∨ valuation q 1307 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E170.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112170
