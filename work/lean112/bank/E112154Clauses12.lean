import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1325 = true := by
  have hs : count1325 q = (countLit q [-83]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (1325)) (countLit q [-83]) (countLit q [-87]) (count1325 q) 1 (meaningNeg87 q) (meaning1325 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1325 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1325 = true := by
  have hs : count1325 q = (countLit q [-83]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1325)) (countLit q [-83]) (countLit q [-87]) (count1325 q) 1 (meaningNeg83 q) (meaning1325 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1325 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 1325 = false ∨ valuationOf q 1327 = true := by
  have hs : count1327 q = (countLit q [-80]) + (countLit q [-83, -87]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-83, -87])
  have hm := merge_right (literal (valuationOf q) (1325)) (literal (valuationOf q) (1327)) (countLit q [-80]) (countLit q [-83, -87]) (count1327 q) 1 (meaning1325 q) (meaning1327 q) hs
  change valuationOf q 1325 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 1325 = false ∨ valuation q 1327 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1327 = true := by
  have hs : count1327 q = (countLit q [-80]) + (countLit q [-83, -87]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-83, -87])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1327)) (countLit q [-80]) (countLit q [-83, -87]) (count1327 q) 1 (meaningNeg80 q) (meaning1327 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1327 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-76, -78, -79]) + (countLit q [-80, -83, -87]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79]) (l₂ := [-80, -83, -87])
  have hm := merge_right (literal (valuationOf q) (1327)) (literal (valuationOf q) (1330)) (countLit q [-76, -78, -79]) (countLit q [-80, -83, -87]) (count1330 q) 1 (meaning1327 q) (meaning1330 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1330 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-76, -78, -79]) + (countLit q [-80, -83, -87]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79]) (l₂ := [-80, -83, -87])
  have hm := merge_left (literal (valuationOf q) (1322)) (literal (valuationOf q) (1330)) (countLit q [-76, -78, -79]) (countLit q [-80, -83, -87]) (count1330 q) 1 (meaning1322 q) (meaning1330 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1330 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1331 = true := by
  have hs : count1330 q = (countLit q [-76, -78, -79]) + (countLit q [-80, -83, -87]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79]) (l₂ := [-80, -83, -87])
  have hm := merge_two (literal (valuationOf q) (1322)) (literal (valuationOf q) (1327)) (literal (valuationOf q) (1331)) (countLit q [-76, -78, -79]) (countLit q [-80, -83, -87]) (count1330 q) 1 1 (meaning1322 q) (meaning1327 q) (meaning1331 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1327 = false ∨ valuation q 1331 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1331 = true := by
  have hs : count1330 q = (countLit q [-76, -78, -79]) + (countLit q [-80, -83, -87]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79]) (l₂ := [-80, -83, -87])
  have hm := merge_left (literal (valuationOf q) (1323)) (literal (valuationOf q) (1331)) (countLit q [-76, -78, -79]) (countLit q [-80, -83, -87]) (count1330 q) 2 (meaning1323 q) (meaning1331 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1331 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1332 = true := by
  have hs : count1330 q = (countLit q [-76, -78, -79]) + (countLit q [-80, -83, -87]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79]) (l₂ := [-80, -83, -87])
  have hm := merge_two (literal (valuationOf q) (1323)) (literal (valuationOf q) (1327)) (literal (valuationOf q) (1332)) (countLit q [-76, -78, -79]) (countLit q [-80, -83, -87]) (count1330 q) 2 1 (meaning1323 q) (meaning1327 q) (meaning1332 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1327 = false ∨ valuation q 1332 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1336 = true := by
  have hs : count1336 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1336)) (countLit q [-91]) (countLit q [-93]) (count1336 q) 1 (meaningNeg93 q) (meaning1336 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1336 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1336 = true := by
  have hs : count1336 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1336)) (countLit q [-91]) (countLit q [-93]) (count1336 q) 1 (meaningNeg91 q) (meaning1336 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1336 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-88]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91, -93])
  have hm := merge_right (literal (valuationOf q) (1336)) (literal (valuationOf q) (1338)) (countLit q [-88]) (countLit q [-91, -93]) (count1338 q) 1 (meaning1336 q) (meaning1338 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1338 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-88]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91, -93])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1338)) (countLit q [-88]) (countLit q [-91, -93]) (count1338 q) 1 (meaningNeg88 q) (meaning1338 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1338 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1336 = false ∨ valuationOf q 1339 = true := by
  have hs : count1338 q = (countLit q [-88]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91, -93])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (1336)) (literal (valuationOf q) (1339)) (countLit q [-88]) (countLit q [-91, -93]) (count1338 q) 1 1 (meaningNeg88 q) (meaning1336 q) (meaning1339 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1336 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1336 = false ∨ valuation q 1339 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_right (literal (valuationOf q) (-95)) (literal (valuationOf q) (1341)) (countLit q [-94]) (countLit q [-95]) (count1341 q) 1 (meaningNeg95 q) (meaning1341 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1341 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1341)) (countLit q [-94]) (countLit q [-95]) (count1341 q) 1 (meaningNeg94 q) (meaning1341 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1341 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 95 = true ∨ valuationOf q 1342 = true := by
  have hs : count1341 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-95)) (literal (valuationOf q) (1342)) (countLit q [-94]) (countLit q [-95]) (count1341 q) 1 1 (meaningNeg94 q) (meaningNeg95 q) (meaning1342 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 95)) = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 95 = true ∨ valuation q 1342 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1343)) (countLit q [-98]) (countLit q [-101]) (count1343 q) 1 (meaningNeg101 q) (meaning1343 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1343 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1343)) (countLit q [-98]) (countLit q [-101]) (count1343 q) 1 (meaningNeg98 q) (meaning1343 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1343 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1345 = true := by
  have hs : count1345 q = (countLit q [-94, -95]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-98, -101])
  have hm := merge_right (literal (valuationOf q) (1343)) (literal (valuationOf q) (1345)) (countLit q [-94, -95]) (countLit q [-98, -101]) (count1345 q) 1 (meaning1343 q) (meaning1345 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1345 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1345 = true := by
  have hs : count1345 q = (countLit q [-94, -95]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-98, -101])
  have hm := merge_left (literal (valuationOf q) (1341)) (literal (valuationOf q) (1345)) (countLit q [-94, -95]) (countLit q [-98, -101]) (count1345 q) 1 (meaning1341 q) (meaning1345 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1345 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1343 = false ∨ valuationOf q 1346 = true := by
  have hs : count1345 q = (countLit q [-94, -95]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-98, -101])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1343)) (literal (valuationOf q) (1346)) (countLit q [-94, -95]) (countLit q [-98, -101]) (count1345 q) 1 1 (meaning1341 q) (meaning1343 q) (meaning1346 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1343 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1343 = false ∨ valuation q 1346 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1346 = true := by
  have hs : count1345 q = (countLit q [-94, -95]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-98, -101])
  have hm := merge_left (literal (valuationOf q) (1342)) (literal (valuationOf q) (1346)) (countLit q [-94, -95]) (countLit q [-98, -101]) (count1345 q) 2 (meaning1342 q) (meaning1346 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1346 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-88, -91, -93]) + (countLit q [-94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -93]) (l₂ := [-94, -95, -98, -101])
  have hm := merge_right (literal (valuationOf q) (1345)) (literal (valuationOf q) (1349)) (countLit q [-88, -91, -93]) (countLit q [-94, -95, -98, -101]) (count1349 q) 1 (meaning1345 q) (meaning1349 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1349 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-88, -91, -93]) + (countLit q [-94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -93]) (l₂ := [-94, -95, -98, -101])
  have hm := merge_left (literal (valuationOf q) (1338)) (literal (valuationOf q) (1349)) (countLit q [-88, -91, -93]) (countLit q [-94, -95, -98, -101]) (count1349 q) 1 (meaning1338 q) (meaning1349 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1349 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-88, -91, -93]) + (countLit q [-94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -93]) (l₂ := [-94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1338)) (literal (valuationOf q) (1345)) (literal (valuationOf q) (1350)) (countLit q [-88, -91, -93]) (countLit q [-94, -95, -98, -101]) (count1349 q) 1 1 (meaning1338 q) (meaning1345 q) (meaning1350 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1345 = false ∨ valuation q 1350 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1351 = true := by
  have hs : count1349 q = (countLit q [-88, -91, -93]) + (countLit q [-94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -93]) (l₂ := [-94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1338)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1351)) (countLit q [-88, -91, -93]) (countLit q [-94, -95, -98, -101]) (count1349 q) 1 2 (meaning1338 q) (meaning1346 q) (meaning1351 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1346 = false ∨ valuation q 1351 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-88, -91, -93]) + (countLit q [-94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -93]) (l₂ := [-94, -95, -98, -101])
  have hm := merge_left (literal (valuationOf q) (1339)) (literal (valuationOf q) (1350)) (countLit q [-88, -91, -93]) (countLit q [-94, -95, -98, -101]) (count1349 q) 2 (meaning1339 q) (meaning1350 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1350 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1351 = true := by
  have hs : count1349 q = (countLit q [-88, -91, -93]) + (countLit q [-94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -93]) (l₂ := [-94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1339)) (literal (valuationOf q) (1345)) (literal (valuationOf q) (1351)) (countLit q [-88, -91, -93]) (countLit q [-94, -95, -98, -101]) (count1349 q) 2 1 (meaning1339 q) (meaning1345 q) (meaning1351 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1345 = false ∨ valuation q 1351 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-76, -78, -79, -80, -83, -87]) + (countLit q [-88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -80, -83, -87]) (l₂ := [-88, -91, -93, -94, -95, -98, -101])
  have hm := merge_right (literal (valuationOf q) (1349)) (literal (valuationOf q) (1356)) (countLit q [-76, -78, -79, -80, -83, -87]) (countLit q [-88, -91, -93, -94, -95, -98, -101]) (count1356 q) 1 (meaning1349 q) (meaning1356 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1356 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1357 = true := by
  have hs : count1356 q = (countLit q [-76, -78, -79, -80, -83, -87]) + (countLit q [-88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -80, -83, -87]) (l₂ := [-88, -91, -93, -94, -95, -98, -101])
  have hm := merge_right (literal (valuationOf q) (1350)) (literal (valuationOf q) (1357)) (countLit q [-76, -78, -79, -80, -83, -87]) (countLit q [-88, -91, -93, -94, -95, -98, -101]) (count1356 q) 2 (meaning1350 q) (meaning1357 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1357 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1358 = true := by
  have hs : count1356 q = (countLit q [-76, -78, -79, -80, -83, -87]) + (countLit q [-88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -80, -83, -87]) (l₂ := [-88, -91, -93, -94, -95, -98, -101])
  have hm := merge_right (literal (valuationOf q) (1351)) (literal (valuationOf q) (1358)) (countLit q [-76, -78, -79, -80, -83, -87]) (countLit q [-88, -91, -93, -94, -95, -98, -101]) (count1356 q) 3 (meaning1351 q) (meaning1358 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1358 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E154.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112154
