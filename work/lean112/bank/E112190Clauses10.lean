import E112190Semantics
import B112E190Inputs
namespace Snake9.Regrowth.E112190
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1438 = true := by
  have hs : count1436 q = (countLit q [-56, -57, -59, -62, -64, -65]) + (countLit q [-66, -69, -71, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65]) (l₂ := [-66, -69, -71, -72, -74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1410)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1438)) (countLit q [-56, -57, -59, -62, -64, -65]) (countLit q [-66, -69, -71, -72, -74, -78, -80]) (count1436 q) 1 2 (meaning1410 q) (meaning1430 q) (meaning1438 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1430 = false ∨ valuation q 1438 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1438 = true := by
  have hs : count1436 q = (countLit q [-56, -57, -59, -62, -64, -65]) + (countLit q [-66, -69, -71, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65]) (l₂ := [-66, -69, -71, -72, -74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1411)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1438)) (countLit q [-56, -57, -59, -62, -64, -65]) (countLit q [-66, -69, -71, -72, -74, -78, -80]) (count1436 q) 2 1 (meaning1411 q) (meaning1429 q) (meaning1438 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1429 = false ∨ valuation q 1438 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1439 = true := by
  have hs : count1436 q = (countLit q [-56, -57, -59, -62, -64, -65]) + (countLit q [-66, -69, -71, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65]) (l₂ := [-66, -69, -71, -72, -74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1411)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1439)) (countLit q [-56, -57, -59, -62, -64, -65]) (countLit q [-66, -69, -71, -72, -74, -78, -80]) (count1436 q) 2 2 (meaning1411 q) (meaning1430 q) (meaning1439 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1430 = false ∨ valuation q 1439 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1439 = true := by
  have hs : count1436 q = (countLit q [-56, -57, -59, -62, -64, -65]) + (countLit q [-66, -69, -71, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65]) (l₂ := [-66, -69, -71, -72, -74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1412)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1439)) (countLit q [-56, -57, -59, -62, -64, -65]) (countLit q [-66, -69, -71, -72, -74, -78, -80]) (count1436 q) 3 1 (meaning1412 q) (meaning1429 q) (meaning1439 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1429 = false ∨ valuation q 1439 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1449 = true := by
  have hs : count1449 q = (countLit q [-82]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1449)) (countLit q [-82]) (countLit q [-85]) (count1449 q) 1 (meaningNeg85 q) (meaning1449 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1449 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1449 = true := by
  have hs : count1449 q = (countLit q [-82]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1449)) (countLit q [-82]) (countLit q [-85]) (count1449 q) 1 (meaningNeg82 q) (meaning1449 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1449 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 85 = true ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-82]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (1450)) (countLit q [-82]) (countLit q [-85]) (count1449 q) 1 1 (meaningNeg82 q) (meaningNeg85 q) (meaning1450 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 1450 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1451 = true := by
  have hs : count1451 q = (countLit q [-81]) + (countLit q [-82, -85]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -85])
  have hm := merge_right (literal (valuationOf q) (1449)) (literal (valuationOf q) (1451)) (countLit q [-81]) (countLit q [-82, -85]) (count1451 q) 1 (meaning1449 q) (meaning1451 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1451 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1451 = true := by
  have hs : count1451 q = (countLit q [-81]) + (countLit q [-82, -85]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -85])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1451)) (countLit q [-81]) (countLit q [-82, -85]) (count1451 q) 1 (meaningNeg81 q) (meaning1451 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1451 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1449 = false ∨ valuationOf q 1452 = true := by
  have hs : count1451 q = (countLit q [-81]) + (countLit q [-82, -85]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -85])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1452)) (countLit q [-81]) (countLit q [-82, -85]) (count1451 q) 1 1 (meaningNeg81 q) (meaning1449 q) (meaning1452 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1449 = false ∨ valuation q 1452 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1450 = false ∨ valuationOf q 1453 = true := by
  have hs : count1451 q = (countLit q [-81]) + (countLit q [-82, -85]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -85])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1453)) (countLit q [-81]) (countLit q [-82, -85]) (count1451 q) 1 2 (meaningNeg81 q) (meaning1450 q) (meaning1453 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1450 = false ∨ valuation q 1453 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-87]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1454)) (countLit q [-87]) (countLit q [-89]) (count1454 q) 1 (meaningNeg89 q) (meaning1454 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1454 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-87]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1454)) (countLit q [-87]) (countLit q [-89]) (count1454 q) 1 (meaningNeg87 q) (meaning1454 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1454 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 89 = true ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-87]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-89)) (literal (valuationOf q) (1455)) (countLit q [-87]) (countLit q [-89]) (count1454 q) 1 1 (meaningNeg87 q) (meaningNeg89 q) (meaning1455 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 89)) = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 89 = true ∨ valuation q 1455 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1456)) (countLit q [-92]) (countLit q [-93]) (count1456 q) 1 (meaningNeg93 q) (meaning1456 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1456 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1456)) (countLit q [-92]) (countLit q [-93]) (count1456 q) 1 (meaningNeg92 q) (meaning1456 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1456 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1457)) (countLit q [-92]) (countLit q [-93]) (count1456 q) 1 1 (meaningNeg92 q) (meaningNeg93 q) (meaning1457 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 93 = true ∨ valuation q 1457 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1458 = true := by
  have hs : count1458 q = (countLit q [-87, -89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -89]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1456)) (literal (valuationOf q) (1458)) (countLit q [-87, -89]) (countLit q [-92, -93]) (count1458 q) 1 (meaning1456 q) (meaning1458 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1458 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1459 = true := by
  have hs : count1458 q = (countLit q [-87, -89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -89]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1457)) (literal (valuationOf q) (1459)) (countLit q [-87, -89]) (countLit q [-92, -93]) (count1458 q) 2 (meaning1457 q) (meaning1459 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1459 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1458 = true := by
  have hs : count1458 q = (countLit q [-87, -89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -89]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (1454)) (literal (valuationOf q) (1458)) (countLit q [-87, -89]) (countLit q [-92, -93]) (count1458 q) 1 (meaning1454 q) (meaning1458 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1458 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1459 = true := by
  have hs : count1458 q = (countLit q [-87, -89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -89]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1459)) (countLit q [-87, -89]) (countLit q [-92, -93]) (count1458 q) 1 1 (meaning1454 q) (meaning1456 q) (meaning1459 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1456 = false ∨ valuation q 1459 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1460 = true := by
  have hs : count1458 q = (countLit q [-87, -89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -89]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1460)) (countLit q [-87, -89]) (countLit q [-92, -93]) (count1458 q) 1 2 (meaning1454 q) (meaning1457 q) (meaning1460 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1457 = false ∨ valuation q 1460 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1459 = true := by
  have hs : count1458 q = (countLit q [-87, -89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -89]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (1455)) (literal (valuationOf q) (1459)) (countLit q [-87, -89]) (countLit q [-92, -93]) (count1458 q) 2 (meaning1455 q) (meaning1459 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1459 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1460 = true := by
  have hs : count1458 q = (countLit q [-87, -89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -89]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1460)) (countLit q [-87, -89]) (countLit q [-92, -93]) (count1458 q) 2 1 (meaning1455 q) (meaning1456 q) (meaning1460 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1456 = false ∨ valuation q 1460 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-81, -82, -85]) + (countLit q [-87, -89, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85]) (l₂ := [-87, -89, -92, -93])
  have hm := merge_right (literal (valuationOf q) (1458)) (literal (valuationOf q) (1462)) (countLit q [-81, -82, -85]) (countLit q [-87, -89, -92, -93]) (count1462 q) 1 (meaning1458 q) (meaning1462 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1462 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1463 = true := by
  have hs : count1462 q = (countLit q [-81, -82, -85]) + (countLit q [-87, -89, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85]) (l₂ := [-87, -89, -92, -93])
  have hm := merge_right (literal (valuationOf q) (1459)) (literal (valuationOf q) (1463)) (countLit q [-81, -82, -85]) (countLit q [-87, -89, -92, -93]) (count1462 q) 2 (meaning1459 q) (meaning1463 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1463 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1464 = true := by
  have hs : count1462 q = (countLit q [-81, -82, -85]) + (countLit q [-87, -89, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85]) (l₂ := [-87, -89, -92, -93])
  have hm := merge_right (literal (valuationOf q) (1460)) (literal (valuationOf q) (1464)) (countLit q [-81, -82, -85]) (countLit q [-87, -89, -92, -93]) (count1462 q) 3 (meaning1460 q) (meaning1464 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1464 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-81, -82, -85]) + (countLit q [-87, -89, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85]) (l₂ := [-87, -89, -92, -93])
  have hm := merge_left (literal (valuationOf q) (1451)) (literal (valuationOf q) (1462)) (countLit q [-81, -82, -85]) (countLit q [-87, -89, -92, -93]) (count1462 q) 1 (meaning1451 q) (meaning1462 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1462 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1463 = true := by
  have hs : count1462 q = (countLit q [-81, -82, -85]) + (countLit q [-87, -89, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85]) (l₂ := [-87, -89, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1463)) (countLit q [-81, -82, -85]) (countLit q [-87, -89, -92, -93]) (count1462 q) 1 1 (meaning1451 q) (meaning1458 q) (meaning1463 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1458 = false ∨ valuation q 1463 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1464 = true := by
  have hs : count1462 q = (countLit q [-81, -82, -85]) + (countLit q [-87, -89, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85]) (l₂ := [-87, -89, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1459)) (literal (valuationOf q) (1464)) (countLit q [-81, -82, -85]) (countLit q [-87, -89, -92, -93]) (count1462 q) 1 2 (meaning1451 q) (meaning1459 q) (meaning1464 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1459 = false ∨ valuation q 1464 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1465 = true := by
  have hs : count1462 q = (countLit q [-81, -82, -85]) + (countLit q [-87, -89, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85]) (l₂ := [-87, -89, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1460)) (literal (valuationOf q) (1465)) (countLit q [-81, -82, -85]) (countLit q [-87, -89, -92, -93]) (count1462 q) 1 3 (meaning1451 q) (meaning1460 q) (meaning1465 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1460 = false ∨ valuation q 1465 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1463 = true := by
  have hs : count1462 q = (countLit q [-81, -82, -85]) + (countLit q [-87, -89, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85]) (l₂ := [-87, -89, -92, -93])
  have hm := merge_left (literal (valuationOf q) (1452)) (literal (valuationOf q) (1463)) (countLit q [-81, -82, -85]) (countLit q [-87, -89, -92, -93]) (count1462 q) 2 (meaning1452 q) (meaning1463 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1463 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E190.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112190
