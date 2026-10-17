import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1529)) (countLit q [-35]) (countLit q [-36]) (count1529 q) 1 (meaningNeg35 q) (meaning1529 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1529 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 36 = true ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (1530)) (countLit q [-35]) (countLit q [-36]) (count1529 q) 1 1 (meaningNeg35 q) (meaningNeg36 q) (meaning1530 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 36 = true ∨ valuation q 1530 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -36])
  have hm := merge_right (literal (valuationOf q) (1529)) (literal (valuationOf q) (1531)) (countLit q [-33]) (countLit q [-35, -36]) (count1531 q) 1 (meaning1529 q) (meaning1531 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1531 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1532 = true := by
  have hs : count1531 q = (countLit q [-33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -36])
  have hm := merge_right (literal (valuationOf q) (1530)) (literal (valuationOf q) (1532)) (countLit q [-33]) (countLit q [-35, -36]) (count1531 q) 2 (meaning1530 q) (meaning1532 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1532 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -36])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1531)) (countLit q [-33]) (countLit q [-35, -36]) (count1531 q) 1 (meaningNeg33 q) (meaning1531 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1531 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1529 = false ∨ valuationOf q 1532 = true := by
  have hs : count1531 q = (countLit q [-33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1532)) (countLit q [-33]) (countLit q [-35, -36]) (count1531 q) 1 1 (meaningNeg33 q) (meaning1529 q) (meaning1532 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1529 = false ∨ valuation q 1532 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1530 = false ∨ valuationOf q 1533 = true := by
  have hs : count1531 q = (countLit q [-33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1533)) (countLit q [-33]) (countLit q [-35, -36]) (count1531 q) 1 2 (meaningNeg33 q) (meaning1530 q) (meaning1533 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1530 = false ∨ valuation q 1533 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1534 = true := by
  have hs : count1534 q = (countLit q [-38]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1534)) (countLit q [-38]) (countLit q [-41]) (count1534 q) 1 (meaningNeg41 q) (meaning1534 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1534 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1534 = true := by
  have hs : count1534 q = (countLit q [-38]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1534)) (countLit q [-38]) (countLit q [-41]) (count1534 q) 1 (meaningNeg38 q) (meaning1534 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1534 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 41 = true ∨ valuationOf q 1535 = true := by
  have hs : count1534 q = (countLit q [-38]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (1535)) (countLit q [-38]) (countLit q [-41]) (count1534 q) 1 1 (meaningNeg38 q) (meaningNeg41 q) (meaning1535 q) hs
  change (! (valuationOf q 38)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 41 = true ∨ valuation q 1535 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1536 = true := by
  have hs : count1536 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1536)) (countLit q [-43]) (countLit q [-44]) (count1536 q) 1 (meaningNeg44 q) (meaning1536 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1536 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1536 = true := by
  have hs : count1536 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1536)) (countLit q [-43]) (countLit q [-44]) (count1536 q) 1 (meaningNeg43 q) (meaning1536 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1536 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1537 = true := by
  have hs : count1536 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1537)) (countLit q [-43]) (countLit q [-44]) (count1536 q) 1 1 (meaningNeg43 q) (meaningNeg44 q) (meaning1537 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 1537 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1538 = true := by
  have hs : count1538 q = (countLit q [-38, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-43, -44])
  have hm := merge_right (literal (valuationOf q) (1536)) (literal (valuationOf q) (1538)) (countLit q [-38, -41]) (countLit q [-43, -44]) (count1538 q) 1 (meaning1536 q) (meaning1538 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1538 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1539 = true := by
  have hs : count1538 q = (countLit q [-38, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-43, -44])
  have hm := merge_right (literal (valuationOf q) (1537)) (literal (valuationOf q) (1539)) (countLit q [-38, -41]) (countLit q [-43, -44]) (count1538 q) 2 (meaning1537 q) (meaning1539 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1539 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1538 = true := by
  have hs : count1538 q = (countLit q [-38, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-43, -44])
  have hm := merge_left (literal (valuationOf q) (1534)) (literal (valuationOf q) (1538)) (countLit q [-38, -41]) (countLit q [-43, -44]) (count1538 q) 1 (meaning1534 q) (meaning1538 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1538 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1539 = true := by
  have hs : count1538 q = (countLit q [-38, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1539)) (countLit q [-38, -41]) (countLit q [-43, -44]) (count1538 q) 1 1 (meaning1534 q) (meaning1536 q) (meaning1539 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1536 = false ∨ valuation q 1539 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1540 = true := by
  have hs : count1538 q = (countLit q [-38, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1540)) (countLit q [-38, -41]) (countLit q [-43, -44]) (count1538 q) 1 2 (meaning1534 q) (meaning1537 q) (meaning1540 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1537 = false ∨ valuation q 1540 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1539 = true := by
  have hs : count1538 q = (countLit q [-38, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-43, -44])
  have hm := merge_left (literal (valuationOf q) (1535)) (literal (valuationOf q) (1539)) (countLit q [-38, -41]) (countLit q [-43, -44]) (count1538 q) 2 (meaning1535 q) (meaning1539 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1539 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1540 = true := by
  have hs : count1538 q = (countLit q [-38, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1540)) (countLit q [-38, -41]) (countLit q [-43, -44]) (count1538 q) 2 1 (meaning1535 q) (meaning1536 q) (meaning1540 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1536 = false ∨ valuation q 1540 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1541 = true := by
  have hs : count1538 q = (countLit q [-38, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1541)) (countLit q [-38, -41]) (countLit q [-43, -44]) (count1538 q) 2 2 (meaning1535 q) (meaning1537 q) (meaning1541 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1537 = false ∨ valuation q 1541 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1542 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_right (literal (valuationOf q) (1538)) (literal (valuationOf q) (1542)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 1 (meaning1538 q) (meaning1542 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1542 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1543 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_right (literal (valuationOf q) (1539)) (literal (valuationOf q) (1543)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 2 (meaning1539 q) (meaning1543 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1543 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1544 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_right (literal (valuationOf q) (1540)) (literal (valuationOf q) (1544)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 3 (meaning1540 q) (meaning1544 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1544 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1545 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_right (literal (valuationOf q) (1541)) (literal (valuationOf q) (1545)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 4 (meaning1541 q) (meaning1545 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1545 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1542 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_left (literal (valuationOf q) (1531)) (literal (valuationOf q) (1542)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 1 (meaning1531 q) (meaning1542 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1542 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1543 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1543)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 1 1 (meaning1531 q) (meaning1538 q) (meaning1543 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1538 = false ∨ valuation q 1543 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1544 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1544)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 1 2 (meaning1531 q) (meaning1539 q) (meaning1544 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1539 = false ∨ valuation q 1544 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1545 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1545)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 1 3 (meaning1531 q) (meaning1540 q) (meaning1545 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1540 = false ∨ valuation q 1545 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1543 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_left (literal (valuationOf q) (1532)) (literal (valuationOf q) (1543)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 2 (meaning1532 q) (meaning1543 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1543 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1544)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 2 1 (meaning1532 q) (meaning1538 q) (meaning1544 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1538 = false ∨ valuation q 1544 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1545 = true := by
  have hs : count1542 q = (countLit q [-33, -35, -36]) + (countLit q [-38, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36]) (l₂ := [-38, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1545)) (countLit q [-33, -35, -36]) (countLit q [-38, -41, -43, -44]) (count1542 q) 2 2 (meaning1532 q) (meaning1539 q) (meaning1545 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1539 = false ∨ valuation q 1545 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E019.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112019
