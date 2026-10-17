import E112205Semantics
import B112E205Inputs
namespace Snake9.Regrowth.E112205
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-104, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -107])
  have hm := merge_left (literal (valuationOf q) (1493)) (literal (valuationOf q) (1497)) (countLit q [-104, -105]) (countLit q [-106, -107]) (count1496 q) 2 (meaning1493 q) (meaning1497 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1497 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1498 = true := by
  have hs : count1496 q = (countLit q [-104, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1498)) (countLit q [-104, -105]) (countLit q [-106, -107]) (count1496 q) 2 1 (meaning1493 q) (meaning1494 q) (meaning1498 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1494 = false ∨ valuation q 1498 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1496)) (literal (valuationOf q) (1500)) (countLit q [-98, -99, -101]) (countLit q [-104, -105, -106, -107]) (count1500 q) 1 (meaning1496 q) (meaning1500 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1500 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1501 = true := by
  have hs : count1500 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1497)) (literal (valuationOf q) (1501)) (countLit q [-98, -99, -101]) (countLit q [-104, -105, -106, -107]) (count1500 q) 2 (meaning1497 q) (meaning1501 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1501 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1502 = true := by
  have hs : count1500 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1498)) (literal (valuationOf q) (1502)) (countLit q [-98, -99, -101]) (countLit q [-104, -105, -106, -107]) (count1500 q) 3 (meaning1498 q) (meaning1502 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1502 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1501 = true := by
  have hs : count1500 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1501)) (countLit q [-98, -99, -101]) (countLit q [-104, -105, -106, -107]) (count1500 q) 1 1 (meaning1489 q) (meaning1496 q) (meaning1501 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1496 = false ∨ valuation q 1501 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1502 = true := by
  have hs : count1500 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1502)) (countLit q [-98, -99, -101]) (countLit q [-104, -105, -106, -107]) (count1500 q) 2 1 (meaning1490 q) (meaning1496 q) (meaning1502 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1496 = false ∨ valuation q 1502 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1503 = true := by
  have hs : count1500 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1503)) (countLit q [-98, -99, -101]) (countLit q [-104, -105, -106, -107]) (count1500 q) 2 2 (meaning1490 q) (meaning1497 q) (meaning1503 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1497 = false ∨ valuation q 1503 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1503 = true := by
  have hs : count1500 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1503)) (countLit q [-98, -99, -101]) (countLit q [-104, -105, -106, -107]) (count1500 q) 3 1 (meaning1491 q) (meaning1496 q) (meaning1503 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1496 = false ∨ valuation q 1503 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -97]) + (countLit q [-98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -97]) (l₂ := [-98, -99, -101, -104, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1500)) (literal (valuationOf q) (1507)) (countLit q [-85, -87, -88, -91, -94, -97]) (countLit q [-98, -99, -101, -104, -105, -106, -107]) (count1507 q) 1 (meaning1500 q) (meaning1507 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1507 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -97]) + (countLit q [-98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -97]) (l₂ := [-98, -99, -101, -104, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1501)) (literal (valuationOf q) (1508)) (countLit q [-85, -87, -88, -91, -94, -97]) (countLit q [-98, -99, -101, -104, -105, -106, -107]) (count1507 q) 2 (meaning1501 q) (meaning1508 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1508 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1509 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -97]) + (countLit q [-98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -97]) (l₂ := [-98, -99, -101, -104, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1502)) (literal (valuationOf q) (1509)) (countLit q [-85, -87, -88, -91, -94, -97]) (countLit q [-98, -99, -101, -104, -105, -106, -107]) (count1507 q) 3 (meaning1502 q) (meaning1509 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1509 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -97]) + (countLit q [-98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -97]) (l₂ := [-98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1508)) (countLit q [-85, -87, -88, -91, -94, -97]) (countLit q [-98, -99, -101, -104, -105, -106, -107]) (count1507 q) 1 1 (meaning1481 q) (meaning1500 q) (meaning1508 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1500 = false ∨ valuation q 1508 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1509 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -97]) + (countLit q [-98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -97]) (l₂ := [-98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1509)) (countLit q [-85, -87, -88, -91, -94, -97]) (countLit q [-98, -99, -101, -104, -105, -106, -107]) (count1507 q) 1 2 (meaning1481 q) (meaning1501 q) (meaning1509 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1501 = false ∨ valuation q 1509 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1510 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -97]) + (countLit q [-98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -97]) (l₂ := [-98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1510)) (countLit q [-85, -87, -88, -91, -94, -97]) (countLit q [-98, -99, -101, -104, -105, -106, -107]) (count1507 q) 1 3 (meaning1481 q) (meaning1502 q) (meaning1510 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1502 = false ∨ valuation q 1510 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1511 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -97]) + (countLit q [-98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -97]) (l₂ := [-98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1511)) (countLit q [-85, -87, -88, -91, -94, -97]) (countLit q [-98, -99, -101, -104, -105, -106, -107]) (count1507 q) 1 4 (meaning1481 q) (meaning1503 q) (meaning1511 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1503 = false ∨ valuation q 1511 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1509 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -97]) + (countLit q [-98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -97]) (l₂ := [-98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1509)) (countLit q [-85, -87, -88, -91, -94, -97]) (countLit q [-98, -99, -101, -104, -105, -106, -107]) (count1507 q) 2 1 (meaning1482 q) (meaning1500 q) (meaning1509 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1500 = false ∨ valuation q 1509 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1510 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -97]) + (countLit q [-98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -97]) (l₂ := [-98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1510)) (countLit q [-85, -87, -88, -91, -94, -97]) (countLit q [-98, -99, -101, -104, -105, -106, -107]) (count1507 q) 2 2 (meaning1482 q) (meaning1501 q) (meaning1510 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1501 = false ∨ valuation q 1510 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1511 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -97]) + (countLit q [-98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -97]) (l₂ := [-98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1511)) (countLit q [-85, -87, -88, -91, -94, -97]) (countLit q [-98, -99, -101, -104, -105, -106, -107]) (count1507 q) 2 3 (meaning1482 q) (meaning1502 q) (meaning1511 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1502 = false ∨ valuation q 1511 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1510 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -97]) + (countLit q [-98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -97]) (l₂ := [-98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1510)) (countLit q [-85, -87, -88, -91, -94, -97]) (countLit q [-98, -99, -101, -104, -105, -106, -107]) (count1507 q) 3 1 (meaning1483 q) (meaning1500 q) (meaning1510 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1500 = false ∨ valuation q 1510 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1511 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -97]) + (countLit q [-98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -97]) (l₂ := [-98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1511)) (countLit q [-85, -87, -88, -91, -94, -97]) (countLit q [-98, -99, -101, -104, -105, -106, -107]) (count1507 q) 3 2 (meaning1483 q) (meaning1501 q) (meaning1511 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1501 = false ∨ valuation q 1511 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1511 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -97]) + (countLit q [-98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -97]) (l₂ := [-98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1484)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1511)) (countLit q [-85, -87, -88, -91, -94, -97]) (countLit q [-98, -99, -101, -104, -105, -106, -107]) (count1507 q) 4 1 (meaning1484 q) (meaning1500 q) (meaning1511 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1500 = false ∨ valuation q 1511 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1521 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1521)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1519 q) 2 1 (meaning1460 q) (meaning1507 q) (meaning1521 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1507 = false ∨ valuation q 1521 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1523 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1523)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1519 q) 2 3 (meaning1460 q) (meaning1509 q) (meaning1523 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1509 = false ∨ valuation q 1523 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1524 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1524)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1519 q) 2 4 (meaning1460 q) (meaning1510 q) (meaning1524 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1510 = false ∨ valuation q 1524 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1525 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1525)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1519 q) 2 5 (meaning1460 q) (meaning1511 q) (meaning1525 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1511 = false ∨ valuation q 1525 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1523 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1523)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1519 q) 3 2 (meaning1461 q) (meaning1508 q) (meaning1523 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1508 = false ∨ valuation q 1523 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1524 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1524)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1519 q) 3 3 (meaning1461 q) (meaning1509 q) (meaning1524 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1509 = false ∨ valuation q 1524 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1525 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1525)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1519 q) 3 4 (meaning1461 q) (meaning1510 q) (meaning1525 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1510 = false ∨ valuation q 1525 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1526 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1526)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1519 q) 3 5 (meaning1461 q) (meaning1511 q) (meaning1526 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1511 = false ∨ valuation q 1526 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1524 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1524)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1519 q) 4 2 (meaning1462 q) (meaning1508 q) (meaning1524 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1508 = false ∨ valuation q 1524 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1525 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1525)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1519 q) 4 3 (meaning1462 q) (meaning1509 q) (meaning1525 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1509 = false ∨ valuation q 1525 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E205.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112205
