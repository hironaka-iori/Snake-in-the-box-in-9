import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1427 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1427)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 1 4 (meaning1357 q) (meaning1413 q) (meaning1427 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1413 = false ∨ valuation q 1427 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1426 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1358)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1426)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 2 2 (meaning1358 q) (meaning1411 q) (meaning1426 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1411 = false ∨ valuation q 1426 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1427 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1358)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1427)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 2 3 (meaning1358 q) (meaning1412 q) (meaning1427 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1412 = false ∨ valuation q 1427 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1426 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1359)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1426)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 3 1 (meaning1359 q) (meaning1410 q) (meaning1426 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1410 = false ∨ valuation q 1426 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1427 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1359)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1427)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 3 2 (meaning1359 q) (meaning1411 q) (meaning1427 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1411 = false ∨ valuation q 1427 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1428 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1359)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1428)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 3 3 (meaning1359 q) (meaning1412 q) (meaning1428 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1412 = false ∨ valuation q 1428 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1426 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_left (literal (valuationOf q) (1360)) (literal (valuationOf q) (1426)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 4 (meaning1360 q) (meaning1426 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1426 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1428 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1360)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1428)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 4 2 (meaning1360 q) (meaning1411 q) (meaning1428 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1411 = false ∨ valuation q 1428 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1429 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1360)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1429)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 4 3 (meaning1360 q) (meaning1412 q) (meaning1429 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1412 = false ∨ valuation q 1429 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1429 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1361)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1429)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 5 2 (meaning1361 q) (meaning1411 q) (meaning1429 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1411 = false ∨ valuation q 1429 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1430 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1361)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1430)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 5 3 (meaning1361 q) (meaning1412 q) (meaning1430 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1412 = false ∨ valuation q 1430 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1428 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_left (literal (valuationOf q) (1362)) (literal (valuationOf q) (1428)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 6 (meaning1362 q) (meaning1428 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1428 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1429 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1429)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 6 1 (meaning1362 q) (meaning1410 q) (meaning1429 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1410 = false ∨ valuation q 1429 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1430 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1430)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 6 2 (meaning1362 q) (meaning1411 q) (meaning1430 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1411 = false ∨ valuation q 1430 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1448 = true := by
  have hs : count1436 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) + (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (l₂ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1448)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1436 q) 5 8 (meaning1312 q) (meaning1430 q) (meaning1448 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1430 = false ∨ valuation q 1448 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1448 = true := by
  have hs : count1436 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) + (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (l₂ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1313)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1448)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1436 q) 6 7 (meaning1313 q) (meaning1429 q) (meaning1448 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1429 = false ∨ valuation q 1448 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1314 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1448 = true := by
  have hs : count1436 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) + (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (l₂ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1314)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1448)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1436 q) 7 6 (meaning1314 q) (meaning1428 q) (meaning1448 q) hs
  change valuationOf q 1314 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1314 = false ∨ valuation q 1428 = false ∨ valuation q 1448 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1315 = false ∨ valuationOf q 1427 = false ∨ valuationOf q 1448 = true := by
  have hs : count1436 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) + (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (l₂ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1315)) (literal (valuationOf q) (1427)) (literal (valuationOf q) (1448)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1436 q) 8 5 (meaning1315 q) (meaning1427 q) (meaning1448 q) hs
  change valuationOf q 1315 = false ∨ valuationOf q 1427 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1315 = false ∨ valuation q 1427 = false ∨ valuation q 1448 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1316 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1448 = true := by
  have hs : count1436 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) + (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (l₂ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1316)) (literal (valuationOf q) (1426)) (literal (valuationOf q) (1448)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1436 q) 9 4 (meaning1316 q) (meaning1426 q) (meaning1448 q) hs
  change valuationOf q 1316 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1316 = false ∨ valuation q 1426 = false ∨ valuation q 1448 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1448 = true := by
  have hs : count1436 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) + (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (l₂ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1317)) (literal (valuationOf q) (1425)) (literal (valuationOf q) (1448)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24, -26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76, -78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1436 q) 10 3 (meaning1317 q) (meaning1425 q) (meaning1448 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1425 = false ∨ valuation q 1448 = true := counterClause1012 (baseVal q)

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false := by
  rw [value1448]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1436 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 7 = false := by
  rw [value2, value3, value6, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (13 : Vertex) (15 : Vertex) (29 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value20, value21, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (162 : Vertex) (163 : Vertex) (178 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value26, value27, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 35 = false := by
  rw [value32, value33, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (188 : Vertex) (189 : Vertex) (190 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 44 = false ∨ valuation q 45 = false := by
  rw [value38, value39, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (229 : Vertex) (244 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value51, value52, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (259 : Vertex) (266 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value53, value54, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (276 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E174.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h⟩

end
end Snake9.Regrowth.E112174
