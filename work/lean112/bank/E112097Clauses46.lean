import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1515 = true := by
  have hs : count1515 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1515)) (countLit q [-24]) (countLit q [-26]) (count1515 q) 1 (meaningNeg24 q) (meaning1515 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1515 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-27]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1517)) (countLit q [-27]) (countLit q [-30]) (count1517 q) 1 (meaningNeg27 q) (meaning1517 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1517 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-24, -26]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-27, -30])
  have hm := merge_left (literal (valuationOf q) (1515)) (literal (valuationOf q) (1519)) (countLit q [-24, -26]) (countLit q [-27, -30]) (count1519 q) 1 (meaning1515 q) (meaning1519 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1519 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-24, -26]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-27, -30])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1520)) (countLit q [-24, -26]) (countLit q [-27, -30]) (count1519 q) 1 1 (meaning1515 q) (meaning1517 q) (meaning1520 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1517 = false ∨ valuation q 1520 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1525 = true := by
  have hs : count1523 q = (countLit q [-16, -17, -19, -23]) + (countLit q [-24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -19, -23]) (l₂ := [-24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1525)) (countLit q [-16, -17, -19, -23]) (countLit q [-24, -26, -27, -30]) (count1523 q) 1 2 (meaning1511 q) (meaning1520 q) (meaning1525 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1520 = false ∨ valuation q 1525 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1525 = true := by
  have hs : count1523 q = (countLit q [-16, -17, -19, -23]) + (countLit q [-24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -19, -23]) (l₂ := [-24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1525)) (countLit q [-16, -17, -19, -23]) (countLit q [-24, -26, -27, -30]) (count1523 q) 2 1 (meaning1512 q) (meaning1519 q) (meaning1525 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1519 = false ∨ valuation q 1525 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1534 = true := by
  have hs : count1531 q = (countLit q [-2, -5, -9, -11, -12, -14, -15]) + (countLit q [-16, -17, -19, -23, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -9, -11, -12, -14, -15]) (l₂ := [-16, -17, -19, -23, -24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1534)) (countLit q [-2, -5, -9, -11, -12, -14, -15]) (countLit q [-16, -17, -19, -23, -24, -26, -27, -30]) (count1531 q) 1 3 (meaning1500 q) (meaning1525 q) (meaning1534 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1525 = false ∨ valuation q 1534 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1548 = true := by
  have hs : count1548 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1548)) (countLit q [-35]) (countLit q [-37]) (count1548 q) 1 (meaningNeg35 q) (meaning1548 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1548 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1550 = true := by
  have hs : count1550 q = (countLit q [-31, -32]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-31, -32]) (l₂ := [-35, -37])
  have hm := merge_right (literal (valuationOf q) (1548)) (literal (valuationOf q) (1550)) (countLit q [-31, -32]) (countLit q [-35, -37]) (count1550 q) 1 (meaning1548 q) (meaning1550 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1550 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1554 = true := by
  have hs : count1554 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1554)) (countLit q [-39]) (countLit q [-41]) (count1554 q) 1 (meaningNeg41 q) (meaning1554 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1554 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-39, -41]) + (countLit q [-42, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-42, -45])
  have hm := merge_left (literal (valuationOf q) (1554)) (literal (valuationOf q) (1558)) (countLit q [-39, -41]) (countLit q [-42, -45]) (count1558 q) 1 (meaning1554 q) (meaning1558 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1558 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1563 = true := by
  have hs : count1562 q = (countLit q [-31, -32, -35, -37]) + (countLit q [-39, -41, -42, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -35, -37]) (l₂ := [-39, -41, -42, -45])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1563)) (countLit q [-31, -32, -35, -37]) (countLit q [-39, -41, -42, -45]) (count1562 q) 1 1 (meaning1550 q) (meaning1558 q) (meaning1563 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1558 = false ∨ valuation q 1563 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1570 = true := by
  have hs : count1570 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1570)) (countLit q [-48]) (countLit q [-49]) (count1570 q) 1 (meaningNeg49 q) (meaning1570 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1570 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 49 = true ∨ valuationOf q 1571 = true := by
  have hs : count1570 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (1571)) (countLit q [-48]) (countLit q [-49]) (count1570 q) 1 1 (meaningNeg48 q) (meaningNeg49 q) (meaning1571 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 1571 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1572 = true := by
  have hs : count1572 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (1572)) (countLit q [-51]) (countLit q [-52]) (count1572 q) 1 (meaningNeg51 q) (meaning1572 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1572 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1575 = true := by
  have hs : count1574 q = (countLit q [-48, -49]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1575)) (countLit q [-48, -49]) (countLit q [-51, -52]) (count1574 q) 1 1 (meaning1570 q) (meaning1572 q) (meaning1575 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1572 = false ∨ valuation q 1575 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1576 = true := by
  have hs : count1574 q = (countLit q [-48, -49]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1576)) (countLit q [-48, -49]) (countLit q [-51, -52]) (count1574 q) 2 1 (meaning1571 q) (meaning1572 q) (meaning1576 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1572 = false ∨ valuation q 1576 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1578)) (countLit q [-56]) (countLit q [-58]) (count1578 q) 1 (meaningNeg58 q) (meaning1578 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1578 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 58 = true ∨ valuationOf q 1579 = true := by
  have hs : count1578 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-58)) (literal (valuationOf q) (1579)) (countLit q [-56]) (countLit q [-58]) (count1578 q) 1 1 (meaningNeg56 q) (meaningNeg58 q) (meaning1579 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 58)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 58 = true ∨ valuation q 1579 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 62 = true ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (1581)) (countLit q [-60]) (countLit q [-62]) (count1580 q) 1 1 (meaningNeg60 q) (meaningNeg62 q) (meaning1581 q) hs
  change (! (valuationOf q 60)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 62 = true ∨ valuation q 1581 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-56, -58]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-56, -58]) (l₂ := [-60, -62])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1584)) (countLit q [-56, -58]) (countLit q [-60, -62]) (count1582 q) 1 2 (meaning1578 q) (meaning1581 q) (meaning1584 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1581 = false ∨ valuation q 1584 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-56, -58]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-56, -58]) (l₂ := [-60, -62])
  have hm := merge_left (literal (valuationOf q) (1579)) (literal (valuationOf q) (1583)) (countLit q [-56, -58]) (countLit q [-60, -62]) (count1582 q) 2 (meaning1579 q) (meaning1583 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1583 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1590 = true := by
  have hs : count1586 q = (countLit q [-48, -49, -51, -52]) + (countLit q [-56, -58, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -51, -52]) (l₂ := [-56, -58, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1590)) (countLit q [-48, -49, -51, -52]) (countLit q [-56, -58, -60, -62]) (count1586 q) 2 3 (meaning1575 q) (meaning1584 q) (meaning1590 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1584 = false ∨ valuation q 1590 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1590 = true := by
  have hs : count1586 q = (countLit q [-48, -49, -51, -52]) + (countLit q [-56, -58, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -51, -52]) (l₂ := [-56, -58, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1590)) (countLit q [-48, -49, -51, -52]) (countLit q [-56, -58, -60, -62]) (count1586 q) 3 2 (meaning1576 q) (meaning1583 q) (meaning1590 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1583 = false ∨ valuation q 1590 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1600 = true := by
  have hs : count1594 q = (countLit q [-31, -32, -35, -37, -39, -41, -42, -45]) + (countLit q [-48, -49, -51, -52, -56, -58, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -35, -37, -39, -41, -42, -45]) (l₂ := [-48, -49, -51, -52, -56, -58, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1600)) (countLit q [-31, -32, -35, -37, -39, -41, -42, -45]) (countLit q [-48, -49, -51, -52, -56, -58, -60, -62]) (count1594 q) 2 5 (meaning1563 q) (meaning1590 q) (meaning1600 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1590 = false ∨ valuation q 1600 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1620 = true := by
  have hs : count1610 q = (countLit q [-2, -5, -9, -11, -12, -14, -15, -16, -17, -19, -23, -24, -26, -27, -30]) + (countLit q [-31, -32, -35, -37, -39, -41, -42, -45, -48, -49, -51, -52, -56, -58, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -9, -11, -12, -14, -15, -16, -17, -19, -23, -24, -26, -27, -30]) (l₂ := [-31, -32, -35, -37, -39, -41, -42, -45, -48, -49, -51, -52, -56, -58, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1620)) (countLit q [-2, -5, -9, -11, -12, -14, -15, -16, -17, -19, -23, -24, -26, -27, -30]) (countLit q [-31, -32, -35, -37, -39, -41, -42, -45, -48, -49, -51, -52, -56, -58, -60, -62]) (count1610 q) 4 7 (meaning1534 q) (meaning1600 q) (meaning1620 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1600 = false ∨ valuation q 1620 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (1632)) (countLit q [-66]) (countLit q [-67]) (count1632 q) 1 (meaningNeg67 q) (meaning1632 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1632 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1632)) (countLit q [-66]) (countLit q [-67]) (count1632 q) 1 (meaningNeg66 q) (meaning1632 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1632 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-63]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66, -67])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1634)) (countLit q [-63]) (countLit q [-66, -67]) (count1634 q) 1 (meaning1632 q) (meaning1634 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1634 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-68]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1637)) (countLit q [-68]) (countLit q [-71]) (count1637 q) 1 (meaningNeg71 q) (meaning1637 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1637 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-68]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1637)) (countLit q [-68]) (countLit q [-71]) (count1637 q) 1 (meaningNeg68 q) (meaning1637 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1637 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-73]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-75])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1639)) (countLit q [-73]) (countLit q [-75]) (count1639 q) 1 (meaningNeg73 q) (meaning1639 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1639 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E097.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112097
