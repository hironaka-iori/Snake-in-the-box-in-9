import E112234Semantics
import B112E234Inputs
namespace Snake9.Regrowth.E112234
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78, -81])
  have hm := merge_right (literal (valuationOf q) (1339)) (literal (valuationOf q) (1341)) (countLit q [-77]) (countLit q [-78, -81]) (count1340 q) 2 (meaning1339 q) (meaning1341 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1341 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78, -81])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1340)) (countLit q [-77]) (countLit q [-78, -81]) (count1340 q) 1 (meaningNeg77 q) (meaning1340 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1340 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1338 = false ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78, -81])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1341)) (countLit q [-77]) (countLit q [-78, -81]) (count1340 q) 1 1 (meaningNeg77 q) (meaning1338 q) (meaning1341 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1338 = false ∨ valuation q 1341 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-85]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1343)) (countLit q [-85]) (countLit q [-88]) (count1343 q) 1 (meaningNeg88 q) (meaning1343 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1343 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-85]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1343)) (countLit q [-85]) (countLit q [-88]) (count1343 q) 1 (meaningNeg85 q) (meaning1343 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1343 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 88 = true ∨ valuationOf q 1344 = true := by
  have hs : count1343 q = (countLit q [-85]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (1344)) (countLit q [-85]) (countLit q [-88]) (count1343 q) 1 1 (meaningNeg85 q) (meaningNeg88 q) (meaning1344 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 88 = true ∨ valuation q 1344 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1345 = true := by
  have hs : count1345 q = (countLit q [-83]) + (countLit q [-85, -88]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85, -88])
  have hm := merge_right (literal (valuationOf q) (1343)) (literal (valuationOf q) (1345)) (countLit q [-83]) (countLit q [-85, -88]) (count1345 q) 1 (meaning1343 q) (meaning1345 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1345 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1346 = true := by
  have hs : count1345 q = (countLit q [-83]) + (countLit q [-85, -88]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85, -88])
  have hm := merge_right (literal (valuationOf q) (1344)) (literal (valuationOf q) (1346)) (countLit q [-83]) (countLit q [-85, -88]) (count1345 q) 2 (meaning1344 q) (meaning1346 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1346 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1345 = true := by
  have hs : count1345 q = (countLit q [-83]) + (countLit q [-85, -88]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85, -88])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1345)) (countLit q [-83]) (countLit q [-85, -88]) (count1345 q) 1 (meaningNeg83 q) (meaning1345 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1345 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1343 = false ∨ valuationOf q 1346 = true := by
  have hs : count1345 q = (countLit q [-83]) + (countLit q [-85, -88]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85, -88])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (1343)) (literal (valuationOf q) (1346)) (countLit q [-83]) (countLit q [-85, -88]) (count1345 q) 1 1 (meaningNeg83 q) (meaning1343 q) (meaning1346 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1343 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1343 = false ∨ valuation q 1346 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1348 = true := by
  have hs : count1348 q = (countLit q [-77, -78, -81]) + (countLit q [-83, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -81]) (l₂ := [-83, -85, -88])
  have hm := merge_right (literal (valuationOf q) (1345)) (literal (valuationOf q) (1348)) (countLit q [-77, -78, -81]) (countLit q [-83, -85, -88]) (count1348 q) 1 (meaning1345 q) (meaning1348 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1348 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1349 = true := by
  have hs : count1348 q = (countLit q [-77, -78, -81]) + (countLit q [-83, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -81]) (l₂ := [-83, -85, -88])
  have hm := merge_right (literal (valuationOf q) (1346)) (literal (valuationOf q) (1349)) (countLit q [-77, -78, -81]) (countLit q [-83, -85, -88]) (count1348 q) 2 (meaning1346 q) (meaning1349 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1349 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1348 = true := by
  have hs : count1348 q = (countLit q [-77, -78, -81]) + (countLit q [-83, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -81]) (l₂ := [-83, -85, -88])
  have hm := merge_left (literal (valuationOf q) (1340)) (literal (valuationOf q) (1348)) (countLit q [-77, -78, -81]) (countLit q [-83, -85, -88]) (count1348 q) 1 (meaning1340 q) (meaning1348 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1348 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1349 = true := by
  have hs : count1348 q = (countLit q [-77, -78, -81]) + (countLit q [-83, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -81]) (l₂ := [-83, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1340)) (literal (valuationOf q) (1345)) (literal (valuationOf q) (1349)) (countLit q [-77, -78, -81]) (countLit q [-83, -85, -88]) (count1348 q) 1 1 (meaning1340 q) (meaning1345 q) (meaning1349 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1345 = false ∨ valuation q 1349 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1350 = true := by
  have hs : count1348 q = (countLit q [-77, -78, -81]) + (countLit q [-83, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -81]) (l₂ := [-83, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1340)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1350)) (countLit q [-77, -78, -81]) (countLit q [-83, -85, -88]) (count1348 q) 1 2 (meaning1340 q) (meaning1346 q) (meaning1350 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1346 = false ∨ valuation q 1350 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1349 = true := by
  have hs : count1348 q = (countLit q [-77, -78, -81]) + (countLit q [-83, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -81]) (l₂ := [-83, -85, -88])
  have hm := merge_left (literal (valuationOf q) (1341)) (literal (valuationOf q) (1349)) (countLit q [-77, -78, -81]) (countLit q [-83, -85, -88]) (count1348 q) 2 (meaning1341 q) (meaning1349 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1349 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1350 = true := by
  have hs : count1348 q = (countLit q [-77, -78, -81]) + (countLit q [-83, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -81]) (l₂ := [-83, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1345)) (literal (valuationOf q) (1350)) (countLit q [-77, -78, -81]) (countLit q [-83, -85, -88]) (count1348 q) 2 1 (meaning1341 q) (meaning1345 q) (meaning1350 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1345 = false ∨ valuation q 1350 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-90]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91, -93])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1356)) (countLit q [-90]) (countLit q [-91, -93]) (count1356 q) 1 (meaningNeg90 q) (meaning1356 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1356 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1359 = true := by
  have hs : count1359 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1359)) (countLit q [-96]) (countLit q [-98]) (count1359 q) 1 (meaningNeg98 q) (meaning1359 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1359 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1359 = true := by
  have hs : count1359 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-96)) (literal (valuationOf q) (1359)) (countLit q [-96]) (countLit q [-98]) (count1359 q) 1 (meaningNeg96 q) (meaning1359 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1359 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1363 = true := by
  have hs : count1363 q = (countLit q [-96, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-99, -101])
  have hm := merge_left (literal (valuationOf q) (1359)) (literal (valuationOf q) (1363)) (countLit q [-96, -98]) (countLit q [-99, -101]) (count1363 q) 1 (meaning1359 q) (meaning1363 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1363 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1367 = true := by
  have hs : count1367 q = (countLit q [-90, -91, -93]) + (countLit q [-96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -93]) (l₂ := [-96, -98, -99, -101])
  have hm := merge_right (literal (valuationOf q) (1363)) (literal (valuationOf q) (1367)) (countLit q [-90, -91, -93]) (countLit q [-96, -98, -99, -101]) (count1367 q) 1 (meaning1363 q) (meaning1367 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1367 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1367 = true := by
  have hs : count1367 q = (countLit q [-90, -91, -93]) + (countLit q [-96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -93]) (l₂ := [-96, -98, -99, -101])
  have hm := merge_left (literal (valuationOf q) (1356)) (literal (valuationOf q) (1367)) (countLit q [-90, -91, -93]) (countLit q [-96, -98, -99, -101]) (count1367 q) 1 (meaning1356 q) (meaning1367 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1367 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 1348 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1375 = true := by
  have hs : count1374 q = (countLit q [-77, -78, -81, -83, -85, -88]) + (countLit q [-90, -91, -93, -96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -81, -83, -85, -88]) (l₂ := [-90, -91, -93, -96, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (1348)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1375)) (countLit q [-77, -78, -81, -83, -85, -88]) (countLit q [-90, -91, -93, -96, -98, -99, -101]) (count1374 q) 1 1 (meaning1348 q) (meaning1367 q) (meaning1375 q) hs
  change valuationOf q 1348 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 1348 = false ∨ valuation q 1367 = false ∨ valuation q 1375 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1375 = true := by
  have hs : count1374 q = (countLit q [-77, -78, -81, -83, -85, -88]) + (countLit q [-90, -91, -93, -96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -81, -83, -85, -88]) (l₂ := [-90, -91, -93, -96, -98, -99, -101])
  have hm := merge_left (literal (valuationOf q) (1349)) (literal (valuationOf q) (1375)) (countLit q [-77, -78, -81, -83, -85, -88]) (countLit q [-90, -91, -93, -96, -98, -99, -101]) (count1374 q) 2 (meaning1349 q) (meaning1375 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1375 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1376 = true := by
  have hs : count1374 q = (countLit q [-77, -78, -81, -83, -85, -88]) + (countLit q [-90, -91, -93, -96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -81, -83, -85, -88]) (l₂ := [-90, -91, -93, -96, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1376)) (countLit q [-77, -78, -81, -83, -85, -88]) (countLit q [-90, -91, -93, -96, -98, -99, -101]) (count1374 q) 2 1 (meaning1349 q) (meaning1367 q) (meaning1376 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1367 = false ∨ valuation q 1376 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1376 = true := by
  have hs : count1374 q = (countLit q [-77, -78, -81, -83, -85, -88]) + (countLit q [-90, -91, -93, -96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -81, -83, -85, -88]) (l₂ := [-90, -91, -93, -96, -98, -99, -101])
  have hm := merge_left (literal (valuationOf q) (1350)) (literal (valuationOf q) (1376)) (countLit q [-77, -78, -81, -83, -85, -88]) (countLit q [-90, -91, -93, -96, -98, -99, -101]) (count1374 q) 3 (meaning1350 q) (meaning1376 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1376 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1377 = true := by
  have hs : count1374 q = (countLit q [-77, -78, -81, -83, -85, -88]) + (countLit q [-90, -91, -93, -96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -81, -83, -85, -88]) (l₂ := [-90, -91, -93, -96, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (1350)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1377)) (countLit q [-77, -78, -81, -83, -85, -88]) (countLit q [-90, -91, -93, -96, -98, -99, -101]) (count1374 q) 3 1 (meaning1350 q) (meaning1367 q) (meaning1377 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1367 = false ∨ valuation q 1377 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1388 = true := by
  have hs : count1385 q = (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) + (countLit q [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) (l₂ := [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1388)) (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) (countLit q [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) (count1385 q) 2 2 (meaning1328 q) (meaning1375 q) (meaning1388 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1375 = false ∨ valuation q 1388 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1389 = true := by
  have hs : count1385 q = (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) + (countLit q [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) (l₂ := [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1389)) (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) (countLit q [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) (count1385 q) 2 3 (meaning1328 q) (meaning1376 q) (meaning1389 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1376 = false ∨ valuation q 1389 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1390 = true := by
  have hs : count1385 q = (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) + (countLit q [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) (l₂ := [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1377)) (literal (valuationOf q) (1390)) (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) (countLit q [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) (count1385 q) 2 4 (meaning1328 q) (meaning1377 q) (meaning1390 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1377 = false ∨ valuation q 1390 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1389 = true := by
  have hs : count1385 q = (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) + (countLit q [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) (l₂ := [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1389)) (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) (countLit q [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) (count1385 q) 3 2 (meaning1329 q) (meaning1375 q) (meaning1389 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1375 = false ∨ valuation q 1389 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E234.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112234
