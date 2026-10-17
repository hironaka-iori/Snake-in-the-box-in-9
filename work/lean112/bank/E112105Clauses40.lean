import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1524 = true := by
  have hs : count1522 q = (countLit q [-7, -10]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-7, -10]) (l₂ := [-13, -16])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1524)) (countLit q [-7, -10]) (countLit q [-13, -16]) (count1522 q) 1 2 (meaning1518 q) (meaning1521 q) (meaning1524 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1521 = false ∨ valuation q 1524 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-2, -4, -6]) + (countLit q [-7, -10, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-7, -10, -13, -16])
  have hm := merge_right (literal (valuationOf q) (1522)) (literal (valuationOf q) (1526)) (countLit q [-2, -4, -6]) (countLit q [-7, -10, -13, -16]) (count1526 q) 1 (meaning1522 q) (meaning1526 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1526 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-2, -4, -6]) + (countLit q [-7, -10, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-7, -10, -13, -16])
  have hm := merge_right (literal (valuationOf q) (1523)) (literal (valuationOf q) (1527)) (countLit q [-2, -4, -6]) (countLit q [-7, -10, -13, -16]) (count1526 q) 2 (meaning1523 q) (meaning1527 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1527 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1528 = true := by
  have hs : count1526 q = (countLit q [-2, -4, -6]) + (countLit q [-7, -10, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-7, -10, -13, -16])
  have hm := merge_right (literal (valuationOf q) (1524)) (literal (valuationOf q) (1528)) (countLit q [-2, -4, -6]) (countLit q [-7, -10, -13, -16]) (count1526 q) 3 (meaning1524 q) (meaning1528 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1528 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-2, -4, -6]) + (countLit q [-7, -10, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-7, -10, -13, -16])
  have hm := merge_left (literal (valuationOf q) (1515)) (literal (valuationOf q) (1526)) (countLit q [-2, -4, -6]) (countLit q [-7, -10, -13, -16]) (count1526 q) 1 (meaning1515 q) (meaning1526 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1526 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-2, -4, -6]) + (countLit q [-7, -10, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-7, -10, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1527)) (countLit q [-2, -4, -6]) (countLit q [-7, -10, -13, -16]) (count1526 q) 1 1 (meaning1515 q) (meaning1522 q) (meaning1527 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1522 = false ∨ valuation q 1527 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1528 = true := by
  have hs : count1526 q = (countLit q [-2, -4, -6]) + (countLit q [-7, -10, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-7, -10, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1528)) (countLit q [-2, -4, -6]) (countLit q [-7, -10, -13, -16]) (count1526 q) 1 2 (meaning1515 q) (meaning1523 q) (meaning1528 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1523 = false ∨ valuation q 1528 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1529 = true := by
  have hs : count1526 q = (countLit q [-2, -4, -6]) + (countLit q [-7, -10, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-7, -10, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1529)) (countLit q [-2, -4, -6]) (countLit q [-7, -10, -13, -16]) (count1526 q) 1 3 (meaning1515 q) (meaning1524 q) (meaning1529 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1524 = false ∨ valuation q 1529 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-2, -4, -6]) + (countLit q [-7, -10, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-7, -10, -13, -16])
  have hm := merge_left (literal (valuationOf q) (1516)) (literal (valuationOf q) (1527)) (countLit q [-2, -4, -6]) (countLit q [-7, -10, -13, -16]) (count1526 q) 2 (meaning1516 q) (meaning1527 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1527 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1528 = true := by
  have hs : count1526 q = (countLit q [-2, -4, -6]) + (countLit q [-7, -10, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-7, -10, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1528)) (countLit q [-2, -4, -6]) (countLit q [-7, -10, -13, -16]) (count1526 q) 2 1 (meaning1516 q) (meaning1522 q) (meaning1528 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1522 = false ∨ valuation q 1528 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1529 = true := by
  have hs : count1526 q = (countLit q [-2, -4, -6]) + (countLit q [-7, -10, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-7, -10, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1529)) (countLit q [-2, -4, -6]) (countLit q [-7, -10, -13, -16]) (count1526 q) 2 2 (meaning1516 q) (meaning1523 q) (meaning1529 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1523 = false ∨ valuation q 1529 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1530 = true := by
  have hs : count1526 q = (countLit q [-2, -4, -6]) + (countLit q [-7, -10, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-7, -10, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1530)) (countLit q [-2, -4, -6]) (countLit q [-7, -10, -13, -16]) (count1526 q) 2 3 (meaning1516 q) (meaning1524 q) (meaning1530 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1524 = false ∨ valuation q 1530 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1529 = true := by
  have hs : count1526 q = (countLit q [-2, -4, -6]) + (countLit q [-7, -10, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-7, -10, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1529)) (countLit q [-2, -4, -6]) (countLit q [-7, -10, -13, -16]) (count1526 q) 3 1 (meaning1517 q) (meaning1522 q) (meaning1529 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1522 = false ∨ valuation q 1529 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1530 = true := by
  have hs : count1526 q = (countLit q [-2, -4, -6]) + (countLit q [-7, -10, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-7, -10, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1530)) (countLit q [-2, -4, -6]) (countLit q [-7, -10, -13, -16]) (count1526 q) 3 2 (meaning1517 q) (meaning1523 q) (meaning1530 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1523 = false ∨ valuation q 1530 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-17]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (1533)) (countLit q [-17]) (countLit q [-20]) (count1533 q) 1 (meaningNeg20 q) (meaning1533 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1533 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-17]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1533)) (countLit q [-17]) (countLit q [-20]) (count1533 q) 1 (meaningNeg17 q) (meaning1533 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1533 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 20 = true ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-17]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-20])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-20)) (literal (valuationOf q) (1534)) (countLit q [-17]) (countLit q [-20]) (count1533 q) 1 1 (meaningNeg17 q) (meaningNeg20 q) (meaning1534 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 20)) = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 20 = true ∨ valuation q 1534 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1535)) (countLit q [-22]) (countLit q [-23]) (count1535 q) 1 (meaningNeg23 q) (meaning1535 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1535 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1535)) (countLit q [-22]) (countLit q [-23]) (count1535 q) 1 (meaningNeg22 q) (meaning1535 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1535 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 23 = true ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (1536)) (countLit q [-22]) (countLit q [-23]) (count1535 q) 1 1 (meaningNeg22 q) (meaningNeg23 q) (meaning1536 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 23 = true ∨ valuation q 1536 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-17, -20]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -20]) (l₂ := [-22, -23])
  have hm := merge_right (literal (valuationOf q) (1535)) (literal (valuationOf q) (1537)) (countLit q [-17, -20]) (countLit q [-22, -23]) (count1537 q) 1 (meaning1535 q) (meaning1537 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1537 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-17, -20]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -20]) (l₂ := [-22, -23])
  have hm := merge_right (literal (valuationOf q) (1536)) (literal (valuationOf q) (1538)) (countLit q [-17, -20]) (countLit q [-22, -23]) (count1537 q) 2 (meaning1536 q) (meaning1538 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1538 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-17, -20]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -20]) (l₂ := [-22, -23])
  have hm := merge_left (literal (valuationOf q) (1533)) (literal (valuationOf q) (1537)) (countLit q [-17, -20]) (countLit q [-22, -23]) (count1537 q) 1 (meaning1533 q) (meaning1537 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1537 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-17, -20]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -20]) (l₂ := [-22, -23])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1538)) (countLit q [-17, -20]) (countLit q [-22, -23]) (count1537 q) 1 1 (meaning1533 q) (meaning1535 q) (meaning1538 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1535 = false ∨ valuation q 1538 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-17, -20]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -20]) (l₂ := [-22, -23])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1539)) (countLit q [-17, -20]) (countLit q [-22, -23]) (count1537 q) 1 2 (meaning1533 q) (meaning1536 q) (meaning1539 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1536 = false ∨ valuation q 1539 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-17, -20]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -20]) (l₂ := [-22, -23])
  have hm := merge_left (literal (valuationOf q) (1534)) (literal (valuationOf q) (1538)) (countLit q [-17, -20]) (countLit q [-22, -23]) (count1537 q) 2 (meaning1534 q) (meaning1538 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1538 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-17, -20]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -20]) (l₂ := [-22, -23])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1539)) (countLit q [-17, -20]) (countLit q [-22, -23]) (count1537 q) 2 1 (meaning1534 q) (meaning1535 q) (meaning1539 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1535 = false ∨ valuation q 1539 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-17, -20]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -20]) (l₂ := [-22, -23])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1540)) (countLit q [-17, -20]) (countLit q [-22, -23]) (count1537 q) 2 2 (meaning1534 q) (meaning1536 q) (meaning1540 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1536 = false ∨ valuation q 1540 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1541 = true := by
  have hs : count1541 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_right (literal (valuationOf q) (-27)) (literal (valuationOf q) (1541)) (countLit q [-25]) (countLit q [-27]) (count1541 q) 1 (meaningNeg27 q) (meaning1541 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1541 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1541 = true := by
  have hs : count1541 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1541)) (countLit q [-25]) (countLit q [-27]) (count1541 q) 1 (meaningNeg25 q) (meaning1541 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1541 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 27 = true ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-27)) (literal (valuationOf q) (1542)) (countLit q [-25]) (countLit q [-27]) (count1541 q) 1 1 (meaningNeg25 q) (meaningNeg27 q) (meaning1542 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 27)) = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 1542 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1543 = true := by
  have hs : count1543 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1543)) (countLit q [-28]) (countLit q [-31]) (count1543 q) 1 (meaningNeg31 q) (meaning1543 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1543 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E105.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112105
