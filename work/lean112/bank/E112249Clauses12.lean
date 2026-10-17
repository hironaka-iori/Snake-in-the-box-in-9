import E112249Semantics
import B112E249Inputs
namespace Snake9.Regrowth.E112249
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1442 = true := by
  have hs : count1442 q = (countLit q [-101, -102]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-103, -104])
  have hm := merge_left (literal (valuationOf q) (1438)) (literal (valuationOf q) (1442)) (countLit q [-101, -102]) (countLit q [-103, -104]) (count1442 q) 1 (meaning1438 q) (meaning1442 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1442 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-94, -95, -97]) + (countLit q [-101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97]) (l₂ := [-101, -102, -103, -104])
  have hm := merge_right (literal (valuationOf q) (1442)) (literal (valuationOf q) (1446)) (countLit q [-94, -95, -97]) (countLit q [-101, -102, -103, -104]) (count1446 q) 1 (meaning1442 q) (meaning1446 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1446 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-94, -95, -97]) + (countLit q [-101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97]) (l₂ := [-101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1447)) (countLit q [-94, -95, -97]) (countLit q [-101, -102, -103, -104]) (count1446 q) 1 1 (meaning1435 q) (meaning1442 q) (meaning1447 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1442 = false ∨ valuation q 1447 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1448 = true := by
  have hs : count1446 q = (countLit q [-94, -95, -97]) + (countLit q [-101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97]) (l₂ := [-101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1448)) (countLit q [-94, -95, -97]) (countLit q [-101, -102, -103, -104]) (count1446 q) 2 1 (meaning1436 q) (meaning1442 q) (meaning1448 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1442 = false ∨ valuation q 1448 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1453 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -86, -89, -92]) + (countLit q [-94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -89, -92]) (l₂ := [-94, -95, -97, -101, -102, -103, -104])
  have hm := merge_right (literal (valuationOf q) (1446)) (literal (valuationOf q) (1453)) (countLit q [-81, -82, -84, -86, -89, -92]) (countLit q [-94, -95, -97, -101, -102, -103, -104]) (count1453 q) 1 (meaning1446 q) (meaning1453 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1453 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1454 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -86, -89, -92]) + (countLit q [-94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -89, -92]) (l₂ := [-94, -95, -97, -101, -102, -103, -104])
  have hm := merge_right (literal (valuationOf q) (1447)) (literal (valuationOf q) (1454)) (countLit q [-81, -82, -84, -86, -89, -92]) (countLit q [-94, -95, -97, -101, -102, -103, -104]) (count1453 q) 2 (meaning1447 q) (meaning1454 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1454 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1455 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -86, -89, -92]) + (countLit q [-94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -89, -92]) (l₂ := [-94, -95, -97, -101, -102, -103, -104])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1455)) (countLit q [-81, -82, -84, -86, -89, -92]) (countLit q [-94, -95, -97, -101, -102, -103, -104]) (count1453 q) 3 (meaning1448 q) (meaning1455 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1455 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1454 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -86, -89, -92]) + (countLit q [-94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -89, -92]) (l₂ := [-94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1454)) (countLit q [-81, -82, -84, -86, -89, -92]) (countLit q [-94, -95, -97, -101, -102, -103, -104]) (count1453 q) 1 1 (meaning1427 q) (meaning1446 q) (meaning1454 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1446 = false ∨ valuation q 1454 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1455 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -86, -89, -92]) + (countLit q [-94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -89, -92]) (l₂ := [-94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1455)) (countLit q [-81, -82, -84, -86, -89, -92]) (countLit q [-94, -95, -97, -101, -102, -103, -104]) (count1453 q) 1 2 (meaning1427 q) (meaning1447 q) (meaning1455 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1447 = false ∨ valuation q 1455 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1456 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -86, -89, -92]) + (countLit q [-94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -89, -92]) (l₂ := [-94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1456)) (countLit q [-81, -82, -84, -86, -89, -92]) (countLit q [-94, -95, -97, -101, -102, -103, -104]) (count1453 q) 1 3 (meaning1427 q) (meaning1448 q) (meaning1456 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1448 = false ∨ valuation q 1456 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1454 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -86, -89, -92]) + (countLit q [-94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -89, -92]) (l₂ := [-94, -95, -97, -101, -102, -103, -104])
  have hm := merge_left (literal (valuationOf q) (1428)) (literal (valuationOf q) (1454)) (countLit q [-81, -82, -84, -86, -89, -92]) (countLit q [-94, -95, -97, -101, -102, -103, -104]) (count1453 q) 2 (meaning1428 q) (meaning1454 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1454 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1455 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -86, -89, -92]) + (countLit q [-94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -89, -92]) (l₂ := [-94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1455)) (countLit q [-81, -82, -84, -86, -89, -92]) (countLit q [-94, -95, -97, -101, -102, -103, -104]) (count1453 q) 2 1 (meaning1428 q) (meaning1446 q) (meaning1455 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1446 = false ∨ valuation q 1455 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1456 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -86, -89, -92]) + (countLit q [-94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -89, -92]) (l₂ := [-94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1456)) (countLit q [-81, -82, -84, -86, -89, -92]) (countLit q [-94, -95, -97, -101, -102, -103, -104]) (count1453 q) 2 2 (meaning1428 q) (meaning1447 q) (meaning1456 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1447 = false ∨ valuation q 1456 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1464 = true := by
  have hs : count1462 q = (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) + (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (l₂ := [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1464)) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1462 q) 1 2 (meaning1408 q) (meaning1454 q) (meaning1464 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1454 = false ∨ valuation q 1464 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1465 = true := by
  have hs : count1462 q = (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) + (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (l₂ := [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1465)) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1462 q) 1 3 (meaning1408 q) (meaning1455 q) (meaning1465 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1455 = false ∨ valuation q 1465 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1466 = true := by
  have hs : count1462 q = (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) + (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (l₂ := [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1466)) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1462 q) 1 4 (meaning1408 q) (meaning1456 q) (meaning1466 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1456 = false ∨ valuation q 1466 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1464 = true := by
  have hs : count1462 q = (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) + (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (l₂ := [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1409)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1464)) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1462 q) 2 1 (meaning1409 q) (meaning1453 q) (meaning1464 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1453 = false ∨ valuation q 1464 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1465 = true := by
  have hs : count1462 q = (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) + (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (l₂ := [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1409)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1465)) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1462 q) 2 2 (meaning1409 q) (meaning1454 q) (meaning1465 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1454 = false ∨ valuation q 1465 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1466 = true := by
  have hs : count1462 q = (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) + (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (l₂ := [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1409)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1466)) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1462 q) 2 3 (meaning1409 q) (meaning1455 q) (meaning1466 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1455 = false ∨ valuation q 1466 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1467 = true := by
  have hs : count1462 q = (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) + (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (l₂ := [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1409)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1467)) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1462 q) 2 4 (meaning1409 q) (meaning1456 q) (meaning1467 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1456 = false ∨ valuation q 1467 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1465 = true := by
  have hs : count1462 q = (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) + (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (l₂ := [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1410)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1465)) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1462 q) 3 1 (meaning1410 q) (meaning1453 q) (meaning1465 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1453 = false ∨ valuation q 1465 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1466 = true := by
  have hs : count1462 q = (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) + (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (l₂ := [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1410)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1466)) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1462 q) 3 2 (meaning1410 q) (meaning1454 q) (meaning1466 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1454 = false ∨ valuation q 1466 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1466 = true := by
  have hs : count1462 q = (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) + (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (l₂ := [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1411)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1466)) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]) (countLit q [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1462 q) 4 1 (meaning1411 q) (meaning1453 q) (meaning1466 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1453 = false ∨ valuation q 1466 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1479 = true := by
  have hs : count1471 q = (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) + (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (l₂ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1369)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1479)) (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1471 q) 3 6 (meaning1369 q) (meaning1467 q) (meaning1479 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1467 = false ∨ valuation q 1479 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1479 = true := by
  have hs : count1471 q = (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) + (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (l₂ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1370)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1479)) (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1471 q) 4 5 (meaning1370 q) (meaning1466 q) (meaning1479 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1466 = false ∨ valuation q 1479 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1479 = true := by
  have hs : count1471 q = (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) + (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (l₂ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1479)) (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1471 q) 5 4 (meaning1371 q) (meaning1465 q) (meaning1479 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1465 = false ∨ valuation q 1479 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1479 = true := by
  have hs : count1471 q = (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) + (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (l₂ := [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1479)) (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (countLit q [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]) (count1471 q) 6 3 (meaning1372 q) (meaning1464 q) (meaning1479 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1464 = false ∨ valuation q 1479 = true := counterClause411 (baseVal q)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false := by
  rw [value1479]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1471 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem block12 (q : Snake 81) (h : Conditions q) : B112E249.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h⟩

end
end Snake9.Regrowth.E112249
