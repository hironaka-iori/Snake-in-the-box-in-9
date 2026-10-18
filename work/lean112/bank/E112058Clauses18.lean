import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1572 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1572)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 4 3 (meaning1542 q) (meaning1561 q) (meaning1572 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1561 = false ∨ valuation q 1572 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1573)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 4 4 (meaning1542 q) (meaning1562 q) (meaning1573 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1562 = false ∨ valuation q 1573 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1571 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1571)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 5 1 (meaning1543 q) (meaning1559 q) (meaning1571 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1559 = false ∨ valuation q 1571 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1572 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1572)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 5 2 (meaning1543 q) (meaning1560 q) (meaning1572 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1560 = false ∨ valuation q 1572 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1573)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 5 3 (meaning1543 q) (meaning1561 q) (meaning1573 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1561 = false ∨ valuation q 1573 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-58, -59, -62, -66, -67, -70, -72]) + (countLit q [-74, -75, -77, -79, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72]) (l₂ := [-74, -75, -77, -79, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1573)) (countLit q [-58, -59, -62, -66, -67, -70, -72]) (countLit q [-74, -75, -77, -79, -82, -85, -87]) (count1566 q) 6 2 (meaning1544 q) (meaning1560 q) (meaning1573 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1560 = false ∨ valuation q 1573 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-90]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1580)) (countLit q [-90]) (countLit q [-94]) (count1580 q) 1 (meaningNeg94 q) (meaning1580 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1580 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-88]) + (countLit q [-90, -94]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -94])
  have hm := merge_right (literal (valuationOf q) (1580)) (literal (valuationOf q) (1582)) (countLit q [-88]) (countLit q [-90, -94]) (count1582 q) 1 (meaning1580 q) (meaning1582 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1582 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-88]) + (countLit q [-90, -94]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -94])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1582)) (countLit q [-88]) (countLit q [-90, -94]) (count1582 q) 1 (meaningNeg88 q) (meaning1582 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1582 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1585)) (countLit q [-95]) (countLit q [-96]) (count1585 q) 1 (meaningNeg96 q) (meaning1585 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1585 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1585)) (countLit q [-95]) (countLit q [-96]) (count1585 q) 1 (meaningNeg95 q) (meaning1585 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1585 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-97]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1587)) (countLit q [-97]) (countLit q [-101]) (count1587 q) 1 (meaningNeg101 q) (meaning1587 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1587 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-95, -96]) + (countLit q [-97, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -101])
  have hm := merge_right (literal (valuationOf q) (1587)) (literal (valuationOf q) (1589)) (countLit q [-95, -96]) (countLit q [-97, -101]) (count1589 q) 1 (meaning1587 q) (meaning1589 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1589 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-95, -96]) + (countLit q [-97, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -101])
  have hm := merge_left (literal (valuationOf q) (1585)) (literal (valuationOf q) (1589)) (countLit q [-95, -96]) (countLit q [-97, -101]) (count1589 q) 1 (meaning1585 q) (meaning1589 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1589 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-95, -96]) + (countLit q [-97, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -101])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1590)) (countLit q [-95, -96]) (countLit q [-97, -101]) (count1589 q) 1 1 (meaning1585 q) (meaning1587 q) (meaning1590 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1587 = false ∨ valuation q 1590 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -96, -97, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -96, -97, -101])
  have hm := merge_right (literal (valuationOf q) (1589)) (literal (valuationOf q) (1593)) (countLit q [-88, -90, -94]) (countLit q [-95, -96, -97, -101]) (count1593 q) 1 (meaning1589 q) (meaning1593 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1593 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -96, -97, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -96, -97, -101])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1594)) (countLit q [-88, -90, -94]) (countLit q [-95, -96, -97, -101]) (count1593 q) 2 (meaning1590 q) (meaning1594 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1594 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -96, -97, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -96, -97, -101])
  have hm := merge_left (literal (valuationOf q) (1582)) (literal (valuationOf q) (1593)) (countLit q [-88, -90, -94]) (countLit q [-95, -96, -97, -101]) (count1593 q) 1 (meaning1582 q) (meaning1593 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1593 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -96, -97, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -96, -97, -101])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1594)) (countLit q [-88, -90, -94]) (countLit q [-95, -96, -97, -101]) (count1593 q) 1 1 (meaning1582 q) (meaning1589 q) (meaning1594 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1589 = false ∨ valuation q 1594 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1595 = true := by
  have hs : count1593 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -96, -97, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -96, -97, -101])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1595)) (countLit q [-88, -90, -94]) (countLit q [-95, -96, -97, -101]) (count1593 q) 1 2 (meaning1582 q) (meaning1590 q) (meaning1595 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1590 = false ∨ valuation q 1595 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1600)) (countLit q [-103]) (countLit q [-104]) (count1600 q) 1 (meaningNeg104 q) (meaning1600 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1600 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1600)) (countLit q [-103]) (countLit q [-104]) (count1600 q) 1 (meaningNeg103 q) (meaning1600 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1600 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 104 = true ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-104)) (literal (valuationOf q) (1601)) (countLit q [-103]) (countLit q [-104]) (count1600 q) 1 1 (meaningNeg103 q) (meaningNeg104 q) (meaning1601 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 104)) = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 1601 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1602)) (countLit q [-106]) (countLit q [-107]) (count1602 q) 1 (meaningNeg107 q) (meaning1602 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1602 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1602)) (countLit q [-106]) (countLit q [-107]) (count1602 q) 1 (meaningNeg106 q) (meaning1602 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1602 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-106)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1603)) (countLit q [-106]) (countLit q [-107]) (count1602 q) 1 1 (meaningNeg106 q) (meaningNeg107 q) (meaning1603 q) hs
  change (! (valuationOf q 106)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 107 = true ∨ valuation q 1603 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-103, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-106, -107])
  have hm := merge_right (literal (valuationOf q) (1602)) (literal (valuationOf q) (1604)) (countLit q [-103, -104]) (countLit q [-106, -107]) (count1604 q) 1 (meaning1602 q) (meaning1604 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1604 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-103, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-106, -107])
  have hm := merge_right (literal (valuationOf q) (1603)) (literal (valuationOf q) (1605)) (countLit q [-103, -104]) (countLit q [-106, -107]) (count1604 q) 2 (meaning1603 q) (meaning1605 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1605 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-103, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-106, -107])
  have hm := merge_left (literal (valuationOf q) (1600)) (literal (valuationOf q) (1604)) (countLit q [-103, -104]) (countLit q [-106, -107]) (count1604 q) 1 (meaning1600 q) (meaning1604 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1604 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-103, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1605)) (countLit q [-103, -104]) (countLit q [-106, -107]) (count1604 q) 1 1 (meaning1600 q) (meaning1602 q) (meaning1605 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1602 = false ∨ valuation q 1605 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-103, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1606)) (countLit q [-103, -104]) (countLit q [-106, -107]) (count1604 q) 1 2 (meaning1600 q) (meaning1603 q) (meaning1606 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1603 = false ∨ valuation q 1606 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-103, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-106, -107])
  have hm := merge_left (literal (valuationOf q) (1601)) (literal (valuationOf q) (1605)) (countLit q [-103, -104]) (countLit q [-106, -107]) (count1604 q) 2 (meaning1601 q) (meaning1605 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1605 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E058.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112058
