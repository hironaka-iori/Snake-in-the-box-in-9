import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1552 = true := by
  have hs : count1551 q = (countLit q [-79]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1552)) (countLit q [-79]) (countLit q [-82]) (count1551 q) 1 1 (meaningNeg79 q) (meaningNeg82 q) (meaning1552 q) hs
  change (! (valuationOf q 79)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 82 = true ∨ valuation q 1552 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (1553)) (countLit q [-85]) (countLit q [-87]) (count1553 q) 1 (meaningNeg87 q) (meaning1553 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1553 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-79, -82]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-79, -82]) (l₂ := [-85, -87])
  have hm := merge_right (literal (valuationOf q) (1553)) (literal (valuationOf q) (1555)) (countLit q [-79, -82]) (countLit q [-85, -87]) (count1555 q) 1 (meaning1553 q) (meaning1555 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1555 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-79, -82]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-79, -82]) (l₂ := [-85, -87])
  have hm := merge_left (literal (valuationOf q) (1551)) (literal (valuationOf q) (1555)) (countLit q [-79, -82]) (countLit q [-85, -87]) (count1555 q) 1 (meaning1551 q) (meaning1555 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1555 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-79, -82]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-79, -82]) (l₂ := [-85, -87])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1556)) (countLit q [-79, -82]) (countLit q [-85, -87]) (count1555 q) 1 1 (meaning1551 q) (meaning1553 q) (meaning1556 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1553 = false ∨ valuation q 1556 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-79, -82]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-79, -82]) (l₂ := [-85, -87])
  have hm := merge_left (literal (valuationOf q) (1552)) (literal (valuationOf q) (1556)) (countLit q [-79, -82]) (countLit q [-85, -87]) (count1555 q) 2 (meaning1552 q) (meaning1556 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1556 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1559 = true := by
  have hs : count1559 q = (countLit q [-74, -75, -77]) + (countLit q [-79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -77]) (l₂ := [-79, -82, -85, -87])
  have hm := merge_right (literal (valuationOf q) (1555)) (literal (valuationOf q) (1559)) (countLit q [-74, -75, -77]) (countLit q [-79, -82, -85, -87]) (count1559 q) 1 (meaning1555 q) (meaning1559 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1559 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-74, -75, -77]) + (countLit q [-79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -77]) (l₂ := [-79, -82, -85, -87])
  have hm := merge_right (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-74, -75, -77]) (countLit q [-79, -82, -85, -87]) (count1559 q) 2 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1559 = true := by
  have hs : count1559 q = (countLit q [-74, -75, -77]) + (countLit q [-79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -77]) (l₂ := [-79, -82, -85, -87])
  have hm := merge_left (literal (valuationOf q) (1548)) (literal (valuationOf q) (1559)) (countLit q [-74, -75, -77]) (countLit q [-79, -82, -85, -87]) (count1559 q) 1 (meaning1548 q) (meaning1559 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1559 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-74, -75, -77]) + (countLit q [-79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -77]) (l₂ := [-79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1560)) (countLit q [-74, -75, -77]) (countLit q [-79, -82, -85, -87]) (count1559 q) 1 1 (meaning1548 q) (meaning1555 q) (meaning1560 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1555 = false ∨ valuation q 1560 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1561 = true := by
  have hs : count1559 q = (countLit q [-74, -75, -77]) + (countLit q [-79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -77]) (l₂ := [-79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1561)) (countLit q [-74, -75, -77]) (countLit q [-79, -82, -85, -87]) (count1559 q) 1 2 (meaning1548 q) (meaning1556 q) (meaning1561 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1556 = false ∨ valuation q 1561 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-74, -75, -77]) + (countLit q [-79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -77]) (l₂ := [-79, -82, -85, -87])
  have hm := merge_left (literal (valuationOf q) (1549)) (literal (valuationOf q) (1560)) (countLit q [-74, -75, -77]) (countLit q [-79, -82, -85, -87]) (count1559 q) 2 (meaning1549 q) (meaning1560 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1560 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1561 = true := by
  have hs : count1559 q = (countLit q [-74, -75, -77]) + (countLit q [-79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -77]) (l₂ := [-79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1561)) (countLit q [-74, -75, -77]) (countLit q [-79, -82, -85, -87]) (count1559 q) 2 1 (meaning1549 q) (meaning1555 q) (meaning1561 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1555 = false ∨ valuation q 1561 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1562 = true := by
  have hs : count1559 q = (countLit q [-74, -75, -77]) + (countLit q [-79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -77]) (l₂ := [-79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1562)) (countLit q [-74, -75, -77]) (countLit q [-79, -82, -85, -87]) (count1559 q) 2 2 (meaning1549 q) (meaning1556 q) (meaning1562 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1556 = false ∨ valuation q 1562 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1561 = true := by
  have hs : count1559 q = (countLit q [-74, -75, -77]) + (countLit q [-79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -77]) (l₂ := [-79, -82, -85, -87])
  have hm := merge_left (literal (valuationOf q) (1550)) (literal (valuationOf q) (1561)) (countLit q [-74, -75, -77]) (countLit q [-79, -82, -85, -87]) (count1559 q) 3 (meaning1550 q) (meaning1561 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1561 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1562 = true := by
  have hs : count1559 q = (countLit q [-74, -75, -77]) + (countLit q [-79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -77]) (l₂ := [-79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1562)) (countLit q [-74, -75, -77]) (countLit q [-79, -82, -85, -87]) (count1559 q) 3 1 (meaning1550 q) (meaning1555 q) (meaning1562 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1555 = false ∨ valuation q 1562 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1563 = true := by
  have hs : count1559 q = (countLit q [-74, -75, -77]) + (countLit q [-79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -77]) (l₂ := [-79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1563)) (countLit q [-74, -75, -77]) (countLit q [-79, -82, -85, -87]) (count1559 q) 3 2 (meaning1550 q) (meaning1556 q) (meaning1563 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1556 = false ∨ valuation q 1563 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1568 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1568)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 1 2 (meaning1539 q) (meaning1560 q) (meaning1568 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1560 = false ∨ valuation q 1568 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1569)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 1 3 (meaning1539 q) (meaning1561 q) (meaning1569 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1561 = false ∨ valuation q 1569 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1570)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 1 4 (meaning1539 q) (meaning1562 q) (meaning1570 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1562 = false ∨ valuation q 1570 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1568 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1568)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 2 1 (meaning1540 q) (meaning1559 q) (meaning1568 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1559 = false ∨ valuation q 1568 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1569)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 2 2 (meaning1540 q) (meaning1560 q) (meaning1569 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1560 = false ∨ valuation q 1569 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1570)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 2 3 (meaning1540 q) (meaning1561 q) (meaning1570 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1561 = false ∨ valuation q 1570 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1571 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1571)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 2 4 (meaning1540 q) (meaning1562 q) (meaning1571 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1562 = false ∨ valuation q 1571 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1569)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 3 1 (meaning1541 q) (meaning1559 q) (meaning1569 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1559 = false ∨ valuation q 1569 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1570)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 3 2 (meaning1541 q) (meaning1560 q) (meaning1570 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1560 = false ∨ valuation q 1570 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1571 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1571)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 3 3 (meaning1541 q) (meaning1561 q) (meaning1571 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1561 = false ∨ valuation q 1571 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1572 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1572)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 3 4 (meaning1541 q) (meaning1562 q) (meaning1572 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1562 = false ∨ valuation q 1572 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1563)) (literal (valuationOf q) (1573)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 3 5 (meaning1541 q) (meaning1563 q) (meaning1573 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1563 = false ∨ valuation q 1573 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_left (literal (valuationOf q) (1542)) (literal (valuationOf q) (1569)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 4 (meaning1542 q) (meaning1569 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1569 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1570)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 4 1 (meaning1542 q) (meaning1559 q) (meaning1570 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1559 = false ∨ valuation q 1570 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1571 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1571)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 4 2 (meaning1542 q) (meaning1560 q) (meaning1571 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1560 = false ∨ valuation q 1571 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E058.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112058
