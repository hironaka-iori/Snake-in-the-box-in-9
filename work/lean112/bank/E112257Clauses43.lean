import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1509 = true := by
  have hs : count1506 q = (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) + (countLit q [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) (l₂ := [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1509)) (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) (countLit q [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (count1506 q) 1 3 (meaning1433 q) (meaning1493 q) (meaning1509 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1493 = false ∨ valuation q 1509 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1509 = true := by
  have hs : count1506 q = (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) + (countLit q [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) (l₂ := [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1509)) (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) (countLit q [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (count1506 q) 2 2 (meaning1434 q) (meaning1492 q) (meaning1509 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1492 = false ∨ valuation q 1509 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1510 = true := by
  have hs : count1506 q = (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) + (countLit q [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) (l₂ := [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1510)) (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) (countLit q [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (count1506 q) 2 3 (meaning1434 q) (meaning1493 q) (meaning1510 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1493 = false ∨ valuation q 1510 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1511 = true := by
  have hs : count1506 q = (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) + (countLit q [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) (l₂ := [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1511)) (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) (countLit q [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (count1506 q) 3 3 (meaning1435 q) (meaning1493 q) (meaning1511 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1493 = false ∨ valuation q 1511 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1511 = true := by
  have hs : count1506 q = (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) + (countLit q [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) (l₂ := [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1511)) (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) (countLit q [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (count1506 q) 4 2 (meaning1436 q) (meaning1492 q) (meaning1511 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1492 = false ∨ valuation q 1511 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1512 = true := by
  have hs : count1506 q = (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) + (countLit q [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) (l₂ := [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1512)) (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27]) (countLit q [-29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (count1506 q) 5 2 (meaning1437 q) (meaning1492 q) (meaning1512 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1492 = false ∨ valuation q 1512 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-58]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-61])
  have hm := merge_right (literal (valuationOf q) (-61)) (literal (valuationOf q) (1524)) (countLit q [-58]) (countLit q [-61]) (count1524 q) 1 (meaningNeg61 q) (meaning1524 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1524 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-57]) + (countLit q [-58, -61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58, -61])
  have hm := merge_right (literal (valuationOf q) (1524)) (literal (valuationOf q) (1526)) (countLit q [-57]) (countLit q [-58, -61]) (count1526 q) 1 (meaning1524 q) (meaning1526 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1526 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-57]) + (countLit q [-58, -61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58, -61])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1527)) (countLit q [-57]) (countLit q [-58, -61]) (count1526 q) 1 1 (meaningNeg57 q) (meaning1524 q) (meaning1527 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1524 = false ∨ valuation q 1527 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (1529)) (countLit q [-65]) (countLit q [-67]) (count1529 q) 1 (meaningNeg67 q) (meaning1529 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1529 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1529)) (countLit q [-65]) (countLit q [-67]) (count1529 q) 1 (meaningNeg65 q) (meaning1529 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1529 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-69]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1531)) (countLit q [-69]) (countLit q [-73]) (count1531 q) 1 (meaningNeg73 q) (meaning1531 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1531 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1532 = true := by
  have hs : count1531 q = (countLit q [-69]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1532)) (countLit q [-69]) (countLit q [-73]) (count1531 q) 1 1 (meaningNeg69 q) (meaningNeg73 q) (meaning1532 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 73 = true ∨ valuation q 1532 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-65, -67]) + (countLit q [-69, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -73])
  have hm := merge_right (literal (valuationOf q) (1531)) (literal (valuationOf q) (1533)) (countLit q [-65, -67]) (countLit q [-69, -73]) (count1533 q) 1 (meaning1531 q) (meaning1533 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1533 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-65, -67]) + (countLit q [-69, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -73])
  have hm := merge_right (literal (valuationOf q) (1532)) (literal (valuationOf q) (1534)) (countLit q [-65, -67]) (countLit q [-69, -73]) (count1533 q) 2 (meaning1532 q) (meaning1534 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1534 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-65, -67]) + (countLit q [-69, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -73])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1534)) (countLit q [-65, -67]) (countLit q [-69, -73]) (count1533 q) 1 1 (meaning1529 q) (meaning1531 q) (meaning1534 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1531 = false ∨ valuation q 1534 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1535 = true := by
  have hs : count1533 q = (countLit q [-65, -67]) + (countLit q [-69, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -73])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1535)) (countLit q [-65, -67]) (countLit q [-69, -73]) (count1533 q) 1 2 (meaning1529 q) (meaning1532 q) (meaning1535 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1532 = false ∨ valuation q 1535 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61]) + (countLit q [-65, -67, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-65, -67, -69, -73])
  have hm := merge_right (literal (valuationOf q) (1534)) (literal (valuationOf q) (1538)) (countLit q [-57, -58, -61]) (countLit q [-65, -67, -69, -73]) (count1537 q) 2 (meaning1534 q) (meaning1538 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1538 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61]) + (countLit q [-65, -67, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-65, -67, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1539)) (countLit q [-57, -58, -61]) (countLit q [-65, -67, -69, -73]) (count1537 q) 1 2 (meaning1526 q) (meaning1534 q) (meaning1539 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1534 = false ∨ valuation q 1539 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61]) + (countLit q [-65, -67, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-65, -67, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1540)) (countLit q [-57, -58, -61]) (countLit q [-65, -67, -69, -73]) (count1537 q) 1 3 (meaning1526 q) (meaning1535 q) (meaning1540 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1535 = false ∨ valuation q 1540 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61]) + (countLit q [-65, -67, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-65, -67, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1539)) (countLit q [-57, -58, -61]) (countLit q [-65, -67, -69, -73]) (count1537 q) 2 1 (meaning1527 q) (meaning1533 q) (meaning1539 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1533 = false ∨ valuation q 1539 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61]) + (countLit q [-65, -67, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-65, -67, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1540)) (countLit q [-57, -58, -61]) (countLit q [-65, -67, -69, -73]) (count1537 q) 2 2 (meaning1527 q) (meaning1534 q) (meaning1540 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1534 = false ∨ valuation q 1540 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1546 = true := by
  have hs : count1546 q = (countLit q [-74]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76, -77])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1546)) (countLit q [-74]) (countLit q [-76, -77]) (count1546 q) 1 (meaningNeg74 q) (meaning1546 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1546 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1549)) (countLit q [-78]) (countLit q [-80]) (count1549 q) 1 (meaningNeg78 q) (meaning1549 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1549 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 80 = true ∨ valuationOf q 1550 = true := by
  have hs : count1549 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (1550)) (countLit q [-78]) (countLit q [-80]) (count1549 q) 1 1 (meaningNeg78 q) (meaningNeg80 q) (meaning1550 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 80 = true ∨ valuation q 1550 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1551)) (countLit q [-83]) (countLit q [-84]) (count1551 q) 1 (meaningNeg84 q) (meaning1551 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1551 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1551)) (countLit q [-83]) (countLit q [-84]) (count1551 q) 1 (meaningNeg83 q) (meaning1551 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1551 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 84 = true ∨ valuationOf q 1552 = true := by
  have hs : count1551 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (1552)) (countLit q [-83]) (countLit q [-84]) (count1551 q) 1 1 (meaningNeg83 q) (meaningNeg84 q) (meaning1552 q) hs
  change (! (valuationOf q 83)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 1552 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-78, -80]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-83, -84])
  have hm := merge_left (literal (valuationOf q) (1549)) (literal (valuationOf q) (1553)) (countLit q [-78, -80]) (countLit q [-83, -84]) (count1553 q) 1 (meaning1549 q) (meaning1553 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1553 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-78, -80]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-83, -84])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1554)) (countLit q [-78, -80]) (countLit q [-83, -84]) (count1553 q) 1 1 (meaning1549 q) (meaning1551 q) (meaning1554 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1551 = false ∨ valuation q 1554 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-78, -80]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-83, -84])
  have hm := merge_left (literal (valuationOf q) (1550)) (literal (valuationOf q) (1554)) (countLit q [-78, -80]) (countLit q [-83, -84]) (count1553 q) 2 (meaning1550 q) (meaning1554 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1554 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1555 = true := by
  have hs : count1553 q = (countLit q [-78, -80]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-83, -84])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1555)) (countLit q [-78, -80]) (countLit q [-83, -84]) (count1553 q) 2 1 (meaning1550 q) (meaning1551 q) (meaning1555 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1551 = false ∨ valuation q 1555 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E257.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112257
