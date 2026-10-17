import E112150Semantics
import B112E150Inputs
namespace Snake9.Regrowth.E112150
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-77]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1392)) (countLit q [-77]) (countLit q [-80]) (count1392 q) 1 (meaningNeg80 q) (meaning1392 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1392 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-77]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1392)) (countLit q [-77]) (countLit q [-80]) (count1392 q) 1 (meaningNeg77 q) (meaning1392 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1392 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 80 = true ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-77]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (1393)) (countLit q [-77]) (countLit q [-80]) (count1392 q) 1 1 (meaningNeg77 q) (meaningNeg80 q) (meaning1393 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 80 = true ∨ valuation q 1393 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1394 = true := by
  have hs : count1394 q = (countLit q [-72, -75]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-77, -80])
  have hm := merge_right (literal (valuationOf q) (1392)) (literal (valuationOf q) (1394)) (countLit q [-72, -75]) (countLit q [-77, -80]) (count1394 q) 1 (meaning1392 q) (meaning1394 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1394 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1395 = true := by
  have hs : count1394 q = (countLit q [-72, -75]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-77, -80])
  have hm := merge_right (literal (valuationOf q) (1393)) (literal (valuationOf q) (1395)) (countLit q [-72, -75]) (countLit q [-77, -80]) (count1394 q) 2 (meaning1393 q) (meaning1395 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1395 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1394 = true := by
  have hs : count1394 q = (countLit q [-72, -75]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-77, -80])
  have hm := merge_left (literal (valuationOf q) (1390)) (literal (valuationOf q) (1394)) (countLit q [-72, -75]) (countLit q [-77, -80]) (count1394 q) 1 (meaning1390 q) (meaning1394 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1394 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1395 = true := by
  have hs : count1394 q = (countLit q [-72, -75]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-77, -80])
  have hm := merge_two (literal (valuationOf q) (1390)) (literal (valuationOf q) (1392)) (literal (valuationOf q) (1395)) (countLit q [-72, -75]) (countLit q [-77, -80]) (count1394 q) 1 1 (meaning1390 q) (meaning1392 q) (meaning1395 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1392 = false ∨ valuation q 1395 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1396 = true := by
  have hs : count1394 q = (countLit q [-72, -75]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-77, -80])
  have hm := merge_two (literal (valuationOf q) (1390)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1396)) (countLit q [-72, -75]) (countLit q [-77, -80]) (count1394 q) 1 2 (meaning1390 q) (meaning1393 q) (meaning1396 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1393 = false ∨ valuation q 1396 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-67, -68, -70]) + (countLit q [-72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-67, -68, -70]) (l₂ := [-72, -75, -77, -80])
  have hm := merge_right (literal (valuationOf q) (1394)) (literal (valuationOf q) (1398)) (countLit q [-67, -68, -70]) (countLit q [-72, -75, -77, -80]) (count1398 q) 1 (meaning1394 q) (meaning1398 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1398 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1399 = true := by
  have hs : count1398 q = (countLit q [-67, -68, -70]) + (countLit q [-72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-67, -68, -70]) (l₂ := [-72, -75, -77, -80])
  have hm := merge_right (literal (valuationOf q) (1395)) (literal (valuationOf q) (1399)) (countLit q [-67, -68, -70]) (countLit q [-72, -75, -77, -80]) (count1398 q) 2 (meaning1395 q) (meaning1399 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1399 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1400 = true := by
  have hs : count1398 q = (countLit q [-67, -68, -70]) + (countLit q [-72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-67, -68, -70]) (l₂ := [-72, -75, -77, -80])
  have hm := merge_right (literal (valuationOf q) (1396)) (literal (valuationOf q) (1400)) (countLit q [-67, -68, -70]) (countLit q [-72, -75, -77, -80]) (count1398 q) 3 (meaning1396 q) (meaning1400 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1400 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-67, -68, -70]) + (countLit q [-72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-67, -68, -70]) (l₂ := [-72, -75, -77, -80])
  have hm := merge_left (literal (valuationOf q) (1387)) (literal (valuationOf q) (1398)) (countLit q [-67, -68, -70]) (countLit q [-72, -75, -77, -80]) (count1398 q) 1 (meaning1387 q) (meaning1398 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1398 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1399 = true := by
  have hs : count1398 q = (countLit q [-67, -68, -70]) + (countLit q [-72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-67, -68, -70]) (l₂ := [-72, -75, -77, -80])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1399)) (countLit q [-67, -68, -70]) (countLit q [-72, -75, -77, -80]) (count1398 q) 1 1 (meaning1387 q) (meaning1394 q) (meaning1399 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1394 = false ∨ valuation q 1399 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1395 = false ∨ valuationOf q 1400 = true := by
  have hs : count1398 q = (countLit q [-67, -68, -70]) + (countLit q [-72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-67, -68, -70]) (l₂ := [-72, -75, -77, -80])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1395)) (literal (valuationOf q) (1400)) (countLit q [-67, -68, -70]) (countLit q [-72, -75, -77, -80]) (count1398 q) 1 2 (meaning1387 q) (meaning1395 q) (meaning1400 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1395 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1395 = false ∨ valuation q 1400 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1396 = false ∨ valuationOf q 1401 = true := by
  have hs : count1398 q = (countLit q [-67, -68, -70]) + (countLit q [-72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-67, -68, -70]) (l₂ := [-72, -75, -77, -80])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1396)) (literal (valuationOf q) (1401)) (countLit q [-67, -68, -70]) (countLit q [-72, -75, -77, -80]) (count1398 q) 1 3 (meaning1387 q) (meaning1396 q) (meaning1401 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1396 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1396 = false ∨ valuation q 1401 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1401 = true := by
  have hs : count1398 q = (countLit q [-67, -68, -70]) + (countLit q [-72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-67, -68, -70]) (l₂ := [-72, -75, -77, -80])
  have hm := merge_two (literal (valuationOf q) (1389)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1401)) (countLit q [-67, -68, -70]) (countLit q [-72, -75, -77, -80]) (count1398 q) 3 1 (meaning1389 q) (meaning1394 q) (meaning1401 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1394 = false ∨ valuation q 1401 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1405 = true := by
  have hs : count1405 q = (countLit q [-54, -56, -58, -61, -64, -66]) + (countLit q [-67, -68, -70, -72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66]) (l₂ := [-67, -68, -70, -72, -75, -77, -80])
  have hm := merge_right (literal (valuationOf q) (1398)) (literal (valuationOf q) (1405)) (countLit q [-54, -56, -58, -61, -64, -66]) (countLit q [-67, -68, -70, -72, -75, -77, -80]) (count1405 q) 1 (meaning1398 q) (meaning1405 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1405 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1406 = true := by
  have hs : count1405 q = (countLit q [-54, -56, -58, -61, -64, -66]) + (countLit q [-67, -68, -70, -72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66]) (l₂ := [-67, -68, -70, -72, -75, -77, -80])
  have hm := merge_right (literal (valuationOf q) (1399)) (literal (valuationOf q) (1406)) (countLit q [-54, -56, -58, -61, -64, -66]) (countLit q [-67, -68, -70, -72, -75, -77, -80]) (count1405 q) 2 (meaning1399 q) (meaning1406 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1406 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1407 = true := by
  have hs : count1405 q = (countLit q [-54, -56, -58, -61, -64, -66]) + (countLit q [-67, -68, -70, -72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66]) (l₂ := [-67, -68, -70, -72, -75, -77, -80])
  have hm := merge_right (literal (valuationOf q) (1400)) (literal (valuationOf q) (1407)) (countLit q [-54, -56, -58, -61, -64, -66]) (countLit q [-67, -68, -70, -72, -75, -77, -80]) (count1405 q) 3 (meaning1400 q) (meaning1407 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1407 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1408 = true := by
  have hs : count1405 q = (countLit q [-54, -56, -58, -61, -64, -66]) + (countLit q [-67, -68, -70, -72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66]) (l₂ := [-67, -68, -70, -72, -75, -77, -80])
  have hm := merge_right (literal (valuationOf q) (1401)) (literal (valuationOf q) (1408)) (countLit q [-54, -56, -58, -61, -64, -66]) (countLit q [-67, -68, -70, -72, -75, -77, -80]) (count1405 q) 4 (meaning1401 q) (meaning1408 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1408 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1405 = true := by
  have hs : count1405 q = (countLit q [-54, -56, -58, -61, -64, -66]) + (countLit q [-67, -68, -70, -72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66]) (l₂ := [-67, -68, -70, -72, -75, -77, -80])
  have hm := merge_left (literal (valuationOf q) (1379)) (literal (valuationOf q) (1405)) (countLit q [-54, -56, -58, -61, -64, -66]) (countLit q [-67, -68, -70, -72, -75, -77, -80]) (count1405 q) 1 (meaning1379 q) (meaning1405 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1405 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1406 = true := by
  have hs : count1405 q = (countLit q [-54, -56, -58, -61, -64, -66]) + (countLit q [-67, -68, -70, -72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66]) (l₂ := [-67, -68, -70, -72, -75, -77, -80])
  have hm := merge_two (literal (valuationOf q) (1379)) (literal (valuationOf q) (1398)) (literal (valuationOf q) (1406)) (countLit q [-54, -56, -58, -61, -64, -66]) (countLit q [-67, -68, -70, -72, -75, -77, -80]) (count1405 q) 1 1 (meaning1379 q) (meaning1398 q) (meaning1406 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1398 = false ∨ valuation q 1406 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1407 = true := by
  have hs : count1405 q = (countLit q [-54, -56, -58, -61, -64, -66]) + (countLit q [-67, -68, -70, -72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66]) (l₂ := [-67, -68, -70, -72, -75, -77, -80])
  have hm := merge_two (literal (valuationOf q) (1379)) (literal (valuationOf q) (1399)) (literal (valuationOf q) (1407)) (countLit q [-54, -56, -58, -61, -64, -66]) (countLit q [-67, -68, -70, -72, -75, -77, -80]) (count1405 q) 1 2 (meaning1379 q) (meaning1399 q) (meaning1407 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1399 = false ∨ valuation q 1407 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1408 = true := by
  have hs : count1405 q = (countLit q [-54, -56, -58, -61, -64, -66]) + (countLit q [-67, -68, -70, -72, -75, -77, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66]) (l₂ := [-67, -68, -70, -72, -75, -77, -80])
  have hm := merge_two (literal (valuationOf q) (1379)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1408)) (countLit q [-54, -56, -58, -61, -64, -66]) (countLit q [-67, -68, -70, -72, -75, -77, -80]) (count1405 q) 1 3 (meaning1379 q) (meaning1400 q) (meaning1408 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1400 = false ∨ valuation q 1408 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1417 = true := by
  have hs : count1417 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1417)) (countLit q [-82]) (countLit q [-84]) (count1417 q) 1 (meaningNeg84 q) (meaning1417 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1417 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1417 = true := by
  have hs : count1417 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1417)) (countLit q [-82]) (countLit q [-84]) (count1417 q) 1 (meaningNeg82 q) (meaning1417 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1417 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 84 = true ∨ valuationOf q 1418 = true := by
  have hs : count1417 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (1418)) (countLit q [-82]) (countLit q [-84]) (count1417 q) 1 1 (meaningNeg82 q) (meaningNeg84 q) (meaning1418 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 1418 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1419 = true := by
  have hs : count1419 q = (countLit q [-81]) + (countLit q [-82, -84]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -84])
  have hm := merge_right (literal (valuationOf q) (1417)) (literal (valuationOf q) (1419)) (countLit q [-81]) (countLit q [-82, -84]) (count1419 q) 1 (meaning1417 q) (meaning1419 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1419 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1420 = true := by
  have hs : count1419 q = (countLit q [-81]) + (countLit q [-82, -84]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -84])
  have hm := merge_right (literal (valuationOf q) (1418)) (literal (valuationOf q) (1420)) (countLit q [-81]) (countLit q [-82, -84]) (count1419 q) 2 (meaning1418 q) (meaning1420 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1420 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1419 = true := by
  have hs : count1419 q = (countLit q [-81]) + (countLit q [-82, -84]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -84])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1419)) (countLit q [-81]) (countLit q [-82, -84]) (count1419 q) 1 (meaningNeg81 q) (meaning1419 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1419 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1417 = false ∨ valuationOf q 1420 = true := by
  have hs : count1419 q = (countLit q [-81]) + (countLit q [-82, -84]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -84])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1420)) (countLit q [-81]) (countLit q [-82, -84]) (count1419 q) 1 1 (meaningNeg81 q) (meaning1417 q) (meaning1420 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1417 = false ∨ valuation q 1420 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1418 = false ∨ valuationOf q 1421 = true := by
  have hs : count1419 q = (countLit q [-81]) + (countLit q [-82, -84]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -84])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1421)) (countLit q [-81]) (countLit q [-82, -84]) (count1419 q) 1 2 (meaningNeg81 q) (meaning1418 q) (meaning1421 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1418 = false ∨ valuation q 1421 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E150.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112150
