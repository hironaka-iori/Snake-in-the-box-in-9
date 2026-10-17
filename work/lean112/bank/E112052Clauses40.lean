import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1573 = true := by
  have hs : count1571 q = (countLit q [-15, -17]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-15, -17]) (l₂ := [-18, -20])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1573)) (countLit q [-15, -17]) (countLit q [-18, -20]) (count1571 q) 1 2 (meaning1567 q) (meaning1570 q) (meaning1573 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1570 = false ∨ valuation q 1573 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-15, -17]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-15, -17]) (l₂ := [-18, -20])
  have hm := merge_left (literal (valuationOf q) (1568)) (literal (valuationOf q) (1572)) (countLit q [-15, -17]) (countLit q [-18, -20]) (count1571 q) 2 (meaning1568 q) (meaning1572 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1572 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1573 = true := by
  have hs : count1571 q = (countLit q [-15, -17]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-15, -17]) (l₂ := [-18, -20])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1573)) (countLit q [-15, -17]) (countLit q [-18, -20]) (count1571 q) 2 1 (meaning1568 q) (meaning1569 q) (meaning1573 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1569 = false ∨ valuation q 1573 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1574 = true := by
  have hs : count1571 q = (countLit q [-15, -17]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-15, -17]) (l₂ := [-18, -20])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1574)) (countLit q [-15, -17]) (countLit q [-18, -20]) (count1571 q) 2 2 (meaning1568 q) (meaning1570 q) (meaning1574 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1570 = false ∨ valuation q 1574 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (1575)) (countLit q [-24]) (countLit q [-25]) (count1575 q) 1 (meaningNeg25 q) (meaning1575 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1575 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1575)) (countLit q [-24]) (countLit q [-25]) (count1575 q) 1 (meaningNeg24 q) (meaning1575 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1575 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 25 = true ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (1576)) (countLit q [-24]) (countLit q [-25]) (count1575 q) 1 1 (meaningNeg24 q) (meaningNeg25 q) (meaning1576 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 1576 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1577 = true := by
  have hs : count1577 q = (countLit q [-27]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-28])
  have hm := merge_right (literal (valuationOf q) (-28)) (literal (valuationOf q) (1577)) (countLit q [-27]) (countLit q [-28]) (count1577 q) 1 (meaningNeg28 q) (meaning1577 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1577 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1577 = true := by
  have hs : count1577 q = (countLit q [-27]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-28])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1577)) (countLit q [-27]) (countLit q [-28]) (count1577 q) 1 (meaningNeg27 q) (meaning1577 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1577 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 28 = true ∨ valuationOf q 1578 = true := by
  have hs : count1577 q = (countLit q [-27]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-28])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (-28)) (literal (valuationOf q) (1578)) (countLit q [-27]) (countLit q [-28]) (count1577 q) 1 1 (meaningNeg27 q) (meaningNeg28 q) (meaning1578 q) hs
  change (! (valuationOf q 27)) = false ∨ (! (valuationOf q 28)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 28 = true ∨ valuation q 1578 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-24, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -28])
  have hm := merge_right (literal (valuationOf q) (1577)) (literal (valuationOf q) (1579)) (countLit q [-24, -25]) (countLit q [-27, -28]) (count1579 q) 1 (meaning1577 q) (meaning1579 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1579 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-24, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -28])
  have hm := merge_right (literal (valuationOf q) (1578)) (literal (valuationOf q) (1580)) (countLit q [-24, -25]) (countLit q [-27, -28]) (count1579 q) 2 (meaning1578 q) (meaning1580 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1580 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-24, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -28])
  have hm := merge_left (literal (valuationOf q) (1575)) (literal (valuationOf q) (1579)) (countLit q [-24, -25]) (countLit q [-27, -28]) (count1579 q) 1 (meaning1575 q) (meaning1579 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1579 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-24, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -28])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1580)) (countLit q [-24, -25]) (countLit q [-27, -28]) (count1579 q) 1 1 (meaning1575 q) (meaning1577 q) (meaning1580 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1577 = false ∨ valuation q 1580 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true := by
  have hs : count1579 q = (countLit q [-24, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -28])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1581)) (countLit q [-24, -25]) (countLit q [-27, -28]) (count1579 q) 1 2 (meaning1575 q) (meaning1578 q) (meaning1581 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1578 = false ∨ valuation q 1581 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-24, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -28])
  have hm := merge_left (literal (valuationOf q) (1576)) (literal (valuationOf q) (1580)) (countLit q [-24, -25]) (countLit q [-27, -28]) (count1579 q) 2 (meaning1576 q) (meaning1580 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1580 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1581 = true := by
  have hs : count1579 q = (countLit q [-24, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -28])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1581)) (countLit q [-24, -25]) (countLit q [-27, -28]) (count1579 q) 2 1 (meaning1576 q) (meaning1577 q) (meaning1581 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1577 = false ∨ valuation q 1581 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1582 = true := by
  have hs : count1579 q = (countLit q [-24, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-27, -28])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1582)) (countLit q [-24, -25]) (countLit q [-27, -28]) (count1579 q) 2 2 (meaning1576 q) (meaning1578 q) (meaning1582 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1578 = false ∨ valuation q 1582 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_right (literal (valuationOf q) (1579)) (literal (valuationOf q) (1583)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 1 (meaning1579 q) (meaning1583 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1583 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_right (literal (valuationOf q) (1580)) (literal (valuationOf q) (1584)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 2 (meaning1580 q) (meaning1584 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1584 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1585 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1585)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 3 (meaning1581 q) (meaning1585 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1585 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1586 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_right (literal (valuationOf q) (1582)) (literal (valuationOf q) (1586)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 4 (meaning1582 q) (meaning1586 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1586 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1584)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 1 1 (meaning1571 q) (meaning1579 q) (meaning1584 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1579 = false ∨ valuation q 1584 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1585 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1585)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 1 2 (meaning1571 q) (meaning1580 q) (meaning1585 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1580 = false ∨ valuation q 1585 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1586 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1586)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 1 3 (meaning1571 q) (meaning1581 q) (meaning1586 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1581 = false ∨ valuation q 1586 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1587 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1587)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 1 4 (meaning1571 q) (meaning1582 q) (meaning1587 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1582 = false ∨ valuation q 1587 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_left (literal (valuationOf q) (1572)) (literal (valuationOf q) (1584)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 2 (meaning1572 q) (meaning1584 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1584 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1585 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1585)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 2 1 (meaning1572 q) (meaning1579 q) (meaning1585 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1579 = false ∨ valuation q 1585 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1586 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1586)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 2 2 (meaning1572 q) (meaning1580 q) (meaning1586 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1580 = false ∨ valuation q 1586 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1587 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1587)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 2 3 (meaning1572 q) (meaning1581 q) (meaning1587 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1581 = false ∨ valuation q 1587 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1585 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_left (literal (valuationOf q) (1573)) (literal (valuationOf q) (1585)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 3 (meaning1573 q) (meaning1585 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1585 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1586 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1586)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 3 1 (meaning1573 q) (meaning1579 q) (meaning1586 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1579 = false ∨ valuation q 1586 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E052.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112052
