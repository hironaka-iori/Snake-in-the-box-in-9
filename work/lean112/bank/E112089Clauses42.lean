import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-14, -15]) + (countLit q [-18, -22]) := List.countP_append (p := literal q) (l₁ := [-14, -15]) (l₂ := [-18, -22])
  have hm := merge_right (literal (valuationOf q) (1527)) (literal (valuationOf q) (1529)) (countLit q [-14, -15]) (countLit q [-18, -22]) (count1529 q) 1 (meaning1527 q) (meaning1529 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1529 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-14, -15]) + (countLit q [-18, -22]) := List.countP_append (p := literal q) (l₁ := [-14, -15]) (l₂ := [-18, -22])
  have hm := merge_right (literal (valuationOf q) (1528)) (literal (valuationOf q) (1530)) (countLit q [-14, -15]) (countLit q [-18, -22]) (count1529 q) 2 (meaning1528 q) (meaning1530 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1530 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-14, -15]) + (countLit q [-18, -22]) := List.countP_append (p := literal q) (l₁ := [-14, -15]) (l₂ := [-18, -22])
  have hm := merge_left (literal (valuationOf q) (1525)) (literal (valuationOf q) (1529)) (countLit q [-14, -15]) (countLit q [-18, -22]) (count1529 q) 1 (meaning1525 q) (meaning1529 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1529 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-14, -15]) + (countLit q [-18, -22]) := List.countP_append (p := literal q) (l₁ := [-14, -15]) (l₂ := [-18, -22])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1530)) (countLit q [-14, -15]) (countLit q [-18, -22]) (count1529 q) 1 1 (meaning1525 q) (meaning1527 q) (meaning1530 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1527 = false ∨ valuation q 1530 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1531 = true := by
  have hs : count1529 q = (countLit q [-14, -15]) + (countLit q [-18, -22]) := List.countP_append (p := literal q) (l₁ := [-14, -15]) (l₂ := [-18, -22])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1531)) (countLit q [-14, -15]) (countLit q [-18, -22]) (count1529 q) 1 2 (meaning1525 q) (meaning1528 q) (meaning1531 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1528 = false ∨ valuation q 1531 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-14, -15]) + (countLit q [-18, -22]) := List.countP_append (p := literal q) (l₁ := [-14, -15]) (l₂ := [-18, -22])
  have hm := merge_left (literal (valuationOf q) (1526)) (literal (valuationOf q) (1530)) (countLit q [-14, -15]) (countLit q [-18, -22]) (count1529 q) 2 (meaning1526 q) (meaning1530 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1530 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1531 = true := by
  have hs : count1529 q = (countLit q [-14, -15]) + (countLit q [-18, -22]) := List.countP_append (p := literal q) (l₁ := [-14, -15]) (l₂ := [-18, -22])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1531)) (countLit q [-14, -15]) (countLit q [-18, -22]) (count1529 q) 2 1 (meaning1526 q) (meaning1527 q) (meaning1531 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1527 = false ∨ valuation q 1531 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1532 = true := by
  have hs : count1529 q = (countLit q [-14, -15]) + (countLit q [-18, -22]) := List.countP_append (p := literal q) (l₁ := [-14, -15]) (l₂ := [-18, -22])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1532)) (countLit q [-14, -15]) (countLit q [-18, -22]) (count1529 q) 2 2 (meaning1526 q) (meaning1528 q) (meaning1532 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1528 = false ∨ valuation q 1532 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (1533)) (countLit q [-24]) (countLit q [-25]) (count1533 q) 1 (meaningNeg25 q) (meaning1533 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1533 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1533)) (countLit q [-24]) (countLit q [-25]) (count1533 q) 1 (meaningNeg24 q) (meaning1533 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1533 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 25 = true ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (1534)) (countLit q [-24]) (countLit q [-25]) (count1533 q) 1 1 (meaningNeg24 q) (meaningNeg25 q) (meaning1534 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 1534 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (1535)) (countLit q [-27]) (countLit q [-29]) (count1535 q) 1 (meaningNeg29 q) (meaning1535 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1535 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1535)) (countLit q [-27]) (countLit q [-29]) (count1535 q) 1 (meaningNeg27 q) (meaning1535 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1535 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 29 = true ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (-29)) (literal (valuationOf q) (1536)) (countLit q [-27]) (countLit q [-29]) (count1535 q) 1 1 (meaningNeg27 q) (meaningNeg29 q) (meaning1536 q) hs
  change (! (valuationOf q 27)) = false ∨ (! (valuationOf q 29)) = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 1536 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-24, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -29])
  have hm := merge_right (literal (valuationOf q) (1535)) (literal (valuationOf q) (1537)) (countLit q [-24, -25]) (countLit q [-27, -29]) (count1537 q) 1 (meaning1535 q) (meaning1537 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1537 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-24, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -29])
  have hm := merge_right (literal (valuationOf q) (1536)) (literal (valuationOf q) (1538)) (countLit q [-24, -25]) (countLit q [-27, -29]) (count1537 q) 2 (meaning1536 q) (meaning1538 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1538 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-24, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (1533)) (literal (valuationOf q) (1537)) (countLit q [-24, -25]) (countLit q [-27, -29]) (count1537 q) 1 (meaning1533 q) (meaning1537 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1537 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-24, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1538)) (countLit q [-24, -25]) (countLit q [-27, -29]) (count1537 q) 1 1 (meaning1533 q) (meaning1535 q) (meaning1538 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1535 = false ∨ valuation q 1538 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-24, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1539)) (countLit q [-24, -25]) (countLit q [-27, -29]) (count1537 q) 1 2 (meaning1533 q) (meaning1536 q) (meaning1539 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1536 = false ∨ valuation q 1539 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-24, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (1534)) (literal (valuationOf q) (1538)) (countLit q [-24, -25]) (countLit q [-27, -29]) (count1537 q) 2 (meaning1534 q) (meaning1538 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1538 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-24, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1539)) (countLit q [-24, -25]) (countLit q [-27, -29]) (count1537 q) 2 1 (meaning1534 q) (meaning1535 q) (meaning1539 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1535 = false ∨ valuation q 1539 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-24, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1540)) (countLit q [-24, -25]) (countLit q [-27, -29]) (count1537 q) 2 2 (meaning1534 q) (meaning1536 q) (meaning1540 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1536 = false ∨ valuation q 1540 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1541 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_right (literal (valuationOf q) (1537)) (literal (valuationOf q) (1541)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 1 (meaning1537 q) (meaning1541 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1541 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_right (literal (valuationOf q) (1538)) (literal (valuationOf q) (1542)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 2 (meaning1538 q) (meaning1542 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1542 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1543 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_right (literal (valuationOf q) (1539)) (literal (valuationOf q) (1543)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 3 (meaning1539 q) (meaning1543 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1543 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_right (literal (valuationOf q) (1540)) (literal (valuationOf q) (1544)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 4 (meaning1540 q) (meaning1544 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1544 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1541 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1529)) (literal (valuationOf q) (1541)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 1 (meaning1529 q) (meaning1541 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1541 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1542)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 1 1 (meaning1529 q) (meaning1537 q) (meaning1542 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1537 = false ∨ valuation q 1542 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1543 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1543)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 1 2 (meaning1529 q) (meaning1538 q) (meaning1543 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1538 = false ∨ valuation q 1543 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1544)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 1 3 (meaning1529 q) (meaning1539 q) (meaning1544 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1539 = false ∨ valuation q 1544 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1545)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 1 4 (meaning1529 q) (meaning1540 q) (meaning1545 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1540 = false ∨ valuation q 1545 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1530)) (literal (valuationOf q) (1542)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 2 (meaning1530 q) (meaning1542 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1542 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E089.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112089
