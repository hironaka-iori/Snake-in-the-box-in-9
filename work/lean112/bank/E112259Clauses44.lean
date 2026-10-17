import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1494 = true := by
  have hs : count1491 q = (countLit q [-29, -31, -33, -35, -37, -40, -41]) + (countLit q [-43, -45, -47, -49, -51, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33, -35, -37, -40, -41]) (l₂ := [-43, -45, -47, -49, -51, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1494)) (countLit q [-29, -31, -33, -35, -37, -40, -41]) (countLit q [-43, -45, -47, -49, -51, -53, -54, -56]) (count1491 q) 2 2 (meaning1461 q) (meaning1484 q) (meaning1494 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1484 = false ∨ valuation q 1494 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1494 = true := by
  have hs : count1491 q = (countLit q [-29, -31, -33, -35, -37, -40, -41]) + (countLit q [-43, -45, -47, -49, -51, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33, -35, -37, -40, -41]) (l₂ := [-43, -45, -47, -49, -51, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1494)) (countLit q [-29, -31, -33, -35, -37, -40, -41]) (countLit q [-43, -45, -47, -49, -51, -53, -54, -56]) (count1491 q) 3 1 (meaning1462 q) (meaning1483 q) (meaning1494 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1483 = false ∨ valuation q 1494 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1509 = true := by
  have hs : count1506 q = (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28]) + (countLit q [-29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28]) (l₂ := [-29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1509)) (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28]) (countLit q [-29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) (count1506 q) 3 1 (meaning1435 q) (meaning1491 q) (meaning1509 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1491 = false ∨ valuation q 1509 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1511 = true := by
  have hs : count1506 q = (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28]) + (countLit q [-29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28]) (l₂ := [-29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1511)) (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28]) (countLit q [-29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) (count1506 q) 3 3 (meaning1435 q) (meaning1493 q) (meaning1511 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1493 = false ∨ valuation q 1511 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1512 = true := by
  have hs : count1506 q = (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28]) + (countLit q [-29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28]) (l₂ := [-29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1512)) (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28]) (countLit q [-29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) (count1506 q) 3 4 (meaning1435 q) (meaning1494 q) (meaning1512 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1494 = false ∨ valuation q 1512 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1510 = true := by
  have hs : count1506 q = (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28]) + (countLit q [-29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28]) (l₂ := [-29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1510)) (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28]) (countLit q [-29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) (count1506 q) 4 1 (meaning1436 q) (meaning1491 q) (meaning1510 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1491 = false ∨ valuation q 1510 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-59]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61])
  have hm := merge_right (literal (valuationOf q) (-61)) (literal (valuationOf q) (1524)) (countLit q [-59]) (countLit q [-61]) (count1524 q) 1 (meaningNeg61 q) (meaning1524 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1524 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-59]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1524)) (countLit q [-59]) (countLit q [-61]) (count1524 q) 1 (meaningNeg59 q) (meaning1524 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1524 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-58]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -61])
  have hm := merge_right (literal (valuationOf q) (1524)) (literal (valuationOf q) (1526)) (countLit q [-58]) (countLit q [-59, -61]) (count1526 q) 1 (meaning1524 q) (meaning1526 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1526 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-58]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -61])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1526)) (countLit q [-58]) (countLit q [-59, -61]) (count1526 q) 1 (meaningNeg58 q) (meaning1526 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1526 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-58]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -61])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1527)) (countLit q [-58]) (countLit q [-59, -61]) (count1526 q) 1 1 (meaningNeg58 q) (meaning1524 q) (meaning1527 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1524 = false ∨ valuation q 1527 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 67 = true ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (1530)) (countLit q [-65]) (countLit q [-67]) (count1529 q) 1 1 (meaningNeg65 q) (meaningNeg67 q) (meaning1530 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 67 = true ∨ valuation q 1530 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1531)) (countLit q [-70]) (countLit q [-71]) (count1531 q) 1 (meaningNeg71 q) (meaning1531 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1531 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1531)) (countLit q [-70]) (countLit q [-71]) (count1531 q) 1 (meaningNeg70 q) (meaning1531 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1531 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 71 = true ∨ valuationOf q 1532 = true := by
  have hs : count1531 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (-71)) (literal (valuationOf q) (1532)) (countLit q [-70]) (countLit q [-71]) (count1531 q) 1 1 (meaningNeg70 q) (meaningNeg71 q) (meaning1532 q) hs
  change (! (valuationOf q 70)) = false ∨ (! (valuationOf q 71)) = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 71 = true ∨ valuation q 1532 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-65, -67]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-70, -71])
  have hm := merge_right (literal (valuationOf q) (1531)) (literal (valuationOf q) (1533)) (countLit q [-65, -67]) (countLit q [-70, -71]) (count1533 q) 1 (meaning1531 q) (meaning1533 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1533 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-65, -67]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-70, -71])
  have hm := merge_left (literal (valuationOf q) (1530)) (literal (valuationOf q) (1534)) (countLit q [-65, -67]) (countLit q [-70, -71]) (count1533 q) 2 (meaning1530 q) (meaning1534 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1534 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1535 = true := by
  have hs : count1533 q = (countLit q [-65, -67]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-70, -71])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1535)) (countLit q [-65, -67]) (countLit q [-70, -71]) (count1533 q) 2 1 (meaning1530 q) (meaning1531 q) (meaning1535 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1531 = false ∨ valuation q 1535 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1536 = true := by
  have hs : count1533 q = (countLit q [-65, -67]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-70, -71])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1536)) (countLit q [-65, -67]) (countLit q [-70, -71]) (count1533 q) 2 2 (meaning1530 q) (meaning1532 q) (meaning1536 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1532 = false ∨ valuation q 1536 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-58, -59, -61]) + (countLit q [-65, -67, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61]) (l₂ := [-65, -67, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1539)) (countLit q [-58, -59, -61]) (countLit q [-65, -67, -70, -71]) (count1537 q) 1 2 (meaning1526 q) (meaning1534 q) (meaning1539 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1534 = false ∨ valuation q 1539 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-58, -59, -61]) + (countLit q [-65, -67, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61]) (l₂ := [-65, -67, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1541)) (countLit q [-58, -59, -61]) (countLit q [-65, -67, -70, -71]) (count1537 q) 1 4 (meaning1526 q) (meaning1536 q) (meaning1541 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1536 = false ∨ valuation q 1541 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-58, -59, -61]) + (countLit q [-65, -67, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61]) (l₂ := [-65, -67, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1539)) (countLit q [-58, -59, -61]) (countLit q [-65, -67, -70, -71]) (count1537 q) 2 1 (meaning1527 q) (meaning1533 q) (meaning1539 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1533 = false ∨ valuation q 1539 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-58, -59, -61]) + (countLit q [-65, -67, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61]) (l₂ := [-65, -67, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1540)) (countLit q [-58, -59, -61]) (countLit q [-65, -67, -70, -71]) (count1537 q) 2 2 (meaning1527 q) (meaning1534 q) (meaning1540 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1534 = false ∨ valuation q 1540 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-58, -59, -61]) + (countLit q [-65, -67, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61]) (l₂ := [-65, -67, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1541)) (countLit q [-58, -59, -61]) (countLit q [-65, -67, -70, -71]) (count1537 q) 2 3 (meaning1527 q) (meaning1535 q) (meaning1541 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1535 = false ∨ valuation q 1541 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1544 = true := by
  have hs : count1544 q = (countLit q [-73]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1544)) (countLit q [-73]) (countLit q [-76]) (count1544 q) 1 (meaningNeg76 q) (meaning1544 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1544 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1544 = true := by
  have hs : count1544 q = (countLit q [-73]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1544)) (countLit q [-73]) (countLit q [-76]) (count1544 q) 1 (meaningNeg73 q) (meaning1544 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1544 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1545 = true := by
  have hs : count1544 q = (countLit q [-73]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-73)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1545)) (countLit q [-73]) (countLit q [-76]) (count1544 q) 1 1 (meaningNeg73 q) (meaningNeg76 q) (meaning1545 q) hs
  change (! (valuationOf q 73)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 76 = true ∨ valuation q 1545 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1546 = true := by
  have hs : count1546 q = (countLit q [-72]) + (countLit q [-73, -76]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -76])
  have hm := merge_right (literal (valuationOf q) (1544)) (literal (valuationOf q) (1546)) (countLit q [-72]) (countLit q [-73, -76]) (count1546 q) 1 (meaning1544 q) (meaning1546 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1546 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1547 = true := by
  have hs : count1546 q = (countLit q [-72]) + (countLit q [-73, -76]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -76])
  have hm := merge_right (literal (valuationOf q) (1545)) (literal (valuationOf q) (1547)) (countLit q [-72]) (countLit q [-73, -76]) (count1546 q) 2 (meaning1545 q) (meaning1547 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1547 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1544 = false ∨ valuationOf q 1547 = true := by
  have hs : count1546 q = (countLit q [-72]) + (countLit q [-73, -76]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -76])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1547)) (countLit q [-72]) (countLit q [-73, -76]) (count1546 q) 1 1 (meaningNeg72 q) (meaning1544 q) (meaning1547 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1544 = false ∨ valuation q 1547 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1545 = false ∨ valuationOf q 1548 = true := by
  have hs : count1546 q = (countLit q [-72]) + (countLit q [-73, -76]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -76])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1548)) (countLit q [-72]) (countLit q [-73, -76]) (count1546 q) 1 2 (meaningNeg72 q) (meaning1545 q) (meaning1548 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1545 = false ∨ valuation q 1548 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1549)) (countLit q [-77]) (countLit q [-79]) (count1549 q) 1 (meaningNeg79 q) (meaning1549 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1549 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E259.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112259
