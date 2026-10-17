import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1544 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_left (literal (valuationOf q) (1533)) (literal (valuationOf q) (1544)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 3 (meaning1533 q) (meaning1544 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1544 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1545 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1545)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 3 1 (meaning1533 q) (meaning1538 q) (meaning1545 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1538 = false ∨ valuation q 1545 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1546 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1546)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 3 2 (meaning1533 q) (meaning1539 q) (meaning1546 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1539 = false ∨ valuation q 1546 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1549)) (countLit q [-46]) (countLit q [-48]) (count1549 q) 1 (meaningNeg48 q) (meaning1549 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1549 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1549)) (countLit q [-46]) (countLit q [-48]) (count1549 q) 1 (meaningNeg46 q) (meaning1549 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1549 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 48 = true ∨ valuationOf q 1550 = true := by
  have hs : count1549 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (1550)) (countLit q [-46]) (countLit q [-48]) (count1549 q) 1 1 (meaningNeg46 q) (meaningNeg48 q) (meaning1550 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 1550 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1551)) (countLit q [-51]) (countLit q [-52]) (count1551 q) 1 (meaningNeg52 q) (meaning1551 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1551 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (1551)) (countLit q [-51]) (countLit q [-52]) (count1551 q) 1 (meaningNeg51 q) (meaning1551 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1551 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 52 = true ∨ valuationOf q 1552 = true := by
  have hs : count1551 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (1552)) (countLit q [-51]) (countLit q [-52]) (count1551 q) 1 1 (meaningNeg51 q) (meaningNeg52 q) (meaning1552 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 1552 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_right (literal (valuationOf q) (1551)) (literal (valuationOf q) (1553)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1553 q) 1 (meaning1551 q) (meaning1553 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1553 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_right (literal (valuationOf q) (1552)) (literal (valuationOf q) (1554)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1553 q) 2 (meaning1552 q) (meaning1554 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1554 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_left (literal (valuationOf q) (1549)) (literal (valuationOf q) (1553)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1553 q) 1 (meaning1549 q) (meaning1553 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1553 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1554)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1553 q) 1 1 (meaning1549 q) (meaning1551 q) (meaning1554 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1551 = false ∨ valuation q 1554 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1555 = true := by
  have hs : count1553 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1555)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1553 q) 1 2 (meaning1549 q) (meaning1552 q) (meaning1555 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1552 = false ∨ valuation q 1555 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_left (literal (valuationOf q) (1550)) (literal (valuationOf q) (1554)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1553 q) 2 (meaning1550 q) (meaning1554 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1554 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1555 = true := by
  have hs : count1553 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1555)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1553 q) 2 1 (meaning1550 q) (meaning1551 q) (meaning1555 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1551 = false ∨ valuation q 1555 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1556 = true := by
  have hs : count1553 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1556)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1553 q) 2 2 (meaning1550 q) (meaning1552 q) (meaning1556 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1552 = false ∨ valuation q 1556 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1557 = true := by
  have hs : count1557 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (1557)) (countLit q [-54]) (countLit q [-55]) (count1557 q) 1 (meaningNeg55 q) (meaning1557 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1557 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1557 = true := by
  have hs : count1557 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1557)) (countLit q [-54]) (countLit q [-55]) (count1557 q) 1 (meaningNeg54 q) (meaning1557 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1557 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 55 = true ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (1558)) (countLit q [-54]) (countLit q [-55]) (count1557 q) 1 1 (meaningNeg54 q) (meaningNeg55 q) (meaning1558 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 1558 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1559 = true := by
  have hs : count1559 q = (countLit q [-58]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1559)) (countLit q [-58]) (countLit q [-61]) (count1559 q) 1 (meaningNeg58 q) (meaning1559 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1559 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1561 = true := by
  have hs : count1561 q = (countLit q [-54, -55]) + (countLit q [-58, -61]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-58, -61])
  have hm := merge_right (literal (valuationOf q) (1559)) (literal (valuationOf q) (1561)) (countLit q [-54, -55]) (countLit q [-58, -61]) (count1561 q) 1 (meaning1559 q) (meaning1561 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1561 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1561 = true := by
  have hs : count1561 q = (countLit q [-54, -55]) + (countLit q [-58, -61]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-58, -61])
  have hm := merge_left (literal (valuationOf q) (1557)) (literal (valuationOf q) (1561)) (countLit q [-54, -55]) (countLit q [-58, -61]) (count1561 q) 1 (meaning1557 q) (meaning1561 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1561 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true := by
  have hs : count1561 q = (countLit q [-54, -55]) + (countLit q [-58, -61]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-58, -61])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1562)) (countLit q [-54, -55]) (countLit q [-58, -61]) (count1561 q) 1 1 (meaning1557 q) (meaning1559 q) (meaning1562 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1559 = false ∨ valuation q 1562 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1562 = true := by
  have hs : count1561 q = (countLit q [-54, -55]) + (countLit q [-58, -61]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-58, -61])
  have hm := merge_left (literal (valuationOf q) (1558)) (literal (valuationOf q) (1562)) (countLit q [-54, -55]) (countLit q [-58, -61]) (count1561 q) 2 (meaning1558 q) (meaning1562 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1562 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1563 = true := by
  have hs : count1561 q = (countLit q [-54, -55]) + (countLit q [-58, -61]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-58, -61])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1563)) (countLit q [-54, -55]) (countLit q [-58, -61]) (count1561 q) 2 1 (meaning1558 q) (meaning1559 q) (meaning1563 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1559 = false ∨ valuation q 1563 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1565 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_right (literal (valuationOf q) (1561)) (literal (valuationOf q) (1565)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 1 (meaning1561 q) (meaning1565 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1565 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1566 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_right (literal (valuationOf q) (1562)) (literal (valuationOf q) (1566)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 2 (meaning1562 q) (meaning1566 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1566 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1567 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_right (literal (valuationOf q) (1563)) (literal (valuationOf q) (1567)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 3 (meaning1563 q) (meaning1567 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1567 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1565 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_left (literal (valuationOf q) (1553)) (literal (valuationOf q) (1565)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 1 (meaning1553 q) (meaning1565 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1565 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1566 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1566)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 1 1 (meaning1553 q) (meaning1561 q) (meaning1566 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1561 = false ∨ valuation q 1566 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1567 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1567)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 1 2 (meaning1553 q) (meaning1562 q) (meaning1567 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1562 = false ∨ valuation q 1567 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E019.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112019
