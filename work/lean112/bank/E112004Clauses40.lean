import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1538 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_left (literal (valuationOf q) (1526)) (literal (valuationOf q) (1538)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 3 (meaning1526 q) (meaning1538 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1538 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1539 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1539)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 3 1 (meaning1526 q) (meaning1532 q) (meaning1539 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1532 = false ∨ valuation q 1539 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1540 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1540)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 3 2 (meaning1526 q) (meaning1533 q) (meaning1540 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1533 = false ∨ valuation q 1540 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1541 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1541)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 3 3 (meaning1526 q) (meaning1534 q) (meaning1541 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1534 = false ∨ valuation q 1541 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1542 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1542)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 3 4 (meaning1526 q) (meaning1535 q) (meaning1542 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1535 = false ∨ valuation q 1542 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1539 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_left (literal (valuationOf q) (1527)) (literal (valuationOf q) (1539)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 4 (meaning1527 q) (meaning1539 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1539 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1540 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1540)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 4 1 (meaning1527 q) (meaning1532 q) (meaning1540 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1532 = false ∨ valuation q 1540 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1541 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1541)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 4 2 (meaning1527 q) (meaning1533 q) (meaning1541 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1533 = false ∨ valuation q 1541 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1542 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1542)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 4 3 (meaning1527 q) (meaning1534 q) (meaning1542 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1534 = false ∨ valuation q 1542 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1543 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1543)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 4 4 (meaning1527 q) (meaning1535 q) (meaning1543 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1535 = false ∨ valuation q 1543 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1546 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1546)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 1 2 (meaning1513 q) (meaning1537 q) (meaning1546 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1537 = false ∨ valuation q 1546 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1547 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1547)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 1 3 (meaning1513 q) (meaning1538 q) (meaning1547 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1538 = false ∨ valuation q 1547 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1548 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1548)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 1 4 (meaning1513 q) (meaning1539 q) (meaning1548 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1539 = false ∨ valuation q 1548 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1549 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1549)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 1 5 (meaning1513 q) (meaning1540 q) (meaning1549 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1540 = false ∨ valuation q 1549 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1550 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1550)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 1 6 (meaning1513 q) (meaning1541 q) (meaning1550 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1541 = false ∨ valuation q 1550 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1551 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1551)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 1 7 (meaning1513 q) (meaning1542 q) (meaning1551 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1542 = false ∨ valuation q 1551 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1552 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1552)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 1 8 (meaning1513 q) (meaning1543 q) (meaning1552 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1543 = false ∨ valuation q 1552 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1546 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1546)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 2 1 (meaning1514 q) (meaning1536 q) (meaning1546 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1536 = false ∨ valuation q 1546 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1547 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1547)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 2 2 (meaning1514 q) (meaning1537 q) (meaning1547 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1537 = false ∨ valuation q 1547 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1548 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1548)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 2 3 (meaning1514 q) (meaning1538 q) (meaning1548 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1538 = false ∨ valuation q 1548 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1549 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1549)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 2 4 (meaning1514 q) (meaning1539 q) (meaning1549 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1539 = false ∨ valuation q 1549 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1550 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1550)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 2 5 (meaning1514 q) (meaning1540 q) (meaning1550 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1540 = false ∨ valuation q 1550 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1551 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1551)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 2 6 (meaning1514 q) (meaning1541 q) (meaning1551 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1541 = false ∨ valuation q 1551 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1552 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1552)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 2 7 (meaning1514 q) (meaning1542 q) (meaning1552 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1542 = false ∨ valuation q 1552 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1553 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1553)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 2 8 (meaning1514 q) (meaning1543 q) (meaning1553 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1543 = false ∨ valuation q 1553 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1547 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1547)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 3 1 (meaning1515 q) (meaning1536 q) (meaning1547 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1536 = false ∨ valuation q 1547 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1548 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1548)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 3 2 (meaning1515 q) (meaning1537 q) (meaning1548 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1537 = false ∨ valuation q 1548 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1549 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1549)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 3 3 (meaning1515 q) (meaning1538 q) (meaning1549 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1538 = false ∨ valuation q 1549 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1550 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1550)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 3 4 (meaning1515 q) (meaning1539 q) (meaning1550 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1539 = false ∨ valuation q 1550 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1551 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1551)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 3 5 (meaning1515 q) (meaning1540 q) (meaning1551 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1540 = false ∨ valuation q 1551 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1552 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1552)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 3 6 (meaning1515 q) (meaning1541 q) (meaning1552 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1541 = false ∨ valuation q 1552 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1553)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 3 7 (meaning1515 q) (meaning1542 q) (meaning1553 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1542 = false ∨ valuation q 1553 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E004.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112004
