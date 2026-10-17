import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-67, -69]) + (countLit q [-71, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-71, -72])
  have hm := merge_left (literal (valuationOf q) (1613)) (literal (valuationOf q) (1617)) (countLit q [-67, -69]) (countLit q [-71, -72]) (count1616 q) 2 (meaning1613 q) (meaning1617 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1617 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-67, -69]) + (countLit q [-71, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-71, -72])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1618)) (countLit q [-67, -69]) (countLit q [-71, -72]) (count1616 q) 2 1 (meaning1613 q) (meaning1614 q) (meaning1618 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1614 = false ∨ valuation q 1618 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-67, -69]) + (countLit q [-71, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-71, -72])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1619)) (countLit q [-67, -69]) (countLit q [-71, -72]) (count1616 q) 2 2 (meaning1613 q) (meaning1615 q) (meaning1619 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1615 = false ∨ valuation q 1619 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1620 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_right (literal (valuationOf q) (1616)) (literal (valuationOf q) (1620)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 1 (meaning1616 q) (meaning1620 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1620 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1621 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_right (literal (valuationOf q) (1617)) (literal (valuationOf q) (1621)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 2 (meaning1617 q) (meaning1621 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1621 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1622 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_right (literal (valuationOf q) (1618)) (literal (valuationOf q) (1622)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 3 (meaning1618 q) (meaning1622 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1622 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1623 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_right (literal (valuationOf q) (1619)) (literal (valuationOf q) (1623)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 4 (meaning1619 q) (meaning1623 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1623 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1620 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_left (literal (valuationOf q) (1609)) (literal (valuationOf q) (1620)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 1 (meaning1609 q) (meaning1620 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1620 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1621 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1621)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 1 1 (meaning1609 q) (meaning1616 q) (meaning1621 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1616 = false ∨ valuation q 1621 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1622 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1622)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 1 2 (meaning1609 q) (meaning1617 q) (meaning1622 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1617 = false ∨ valuation q 1622 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1623 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1623)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 1 3 (meaning1609 q) (meaning1618 q) (meaning1623 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1618 = false ∨ valuation q 1623 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1624 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1624)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 1 4 (meaning1609 q) (meaning1619 q) (meaning1624 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1619 = false ∨ valuation q 1624 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1621 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_left (literal (valuationOf q) (1610)) (literal (valuationOf q) (1621)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 2 (meaning1610 q) (meaning1621 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1621 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1622 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1622)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 2 1 (meaning1610 q) (meaning1616 q) (meaning1622 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1616 = false ∨ valuation q 1622 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1623 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1623)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 2 2 (meaning1610 q) (meaning1617 q) (meaning1623 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1617 = false ∨ valuation q 1623 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1624 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1624)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 2 3 (meaning1610 q) (meaning1618 q) (meaning1624 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1618 = false ∨ valuation q 1624 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1625 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1625)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 2 4 (meaning1610 q) (meaning1619 q) (meaning1625 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1619 = false ∨ valuation q 1625 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1622 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_left (literal (valuationOf q) (1611)) (literal (valuationOf q) (1622)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 3 (meaning1611 q) (meaning1622 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1622 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1623 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1623)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 3 1 (meaning1611 q) (meaning1616 q) (meaning1623 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1616 = false ∨ valuation q 1623 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1624 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1624)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 3 2 (meaning1611 q) (meaning1617 q) (meaning1624 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1617 = false ∨ valuation q 1624 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1625 = true := by
  have hs : count1620 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -69, -71, -72]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -69, -71, -72])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1625)) (countLit q [-63, -64, -66]) (countLit q [-67, -69, -71, -72]) (count1620 q) 3 3 (meaning1611 q) (meaning1618 q) (meaning1625 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1618 = false ∨ valuation q 1625 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1627 = true := by
  have hs : count1627 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1627)) (countLit q [-75]) (countLit q [-76]) (count1627 q) 1 (meaningNeg76 q) (meaning1627 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1627 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1627 = true := by
  have hs : count1627 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1627)) (countLit q [-75]) (countLit q [-76]) (count1627 q) 1 (meaningNeg75 q) (meaning1627 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1627 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1628 = true := by
  have hs : count1627 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1628)) (countLit q [-75]) (countLit q [-76]) (count1627 q) 1 1 (meaningNeg75 q) (meaningNeg76 q) (meaning1628 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 76 = true ∨ valuation q 1628 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1629 = true := by
  have hs : count1629 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1629)) (countLit q [-80]) (countLit q [-81]) (count1629 q) 1 (meaningNeg81 q) (meaning1629 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1629 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1629 = true := by
  have hs : count1629 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1629)) (countLit q [-80]) (countLit q [-81]) (count1629 q) 1 (meaningNeg80 q) (meaning1629 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1629 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1630 = true := by
  have hs : count1629 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1630)) (countLit q [-80]) (countLit q [-81]) (count1629 q) 1 1 (meaningNeg80 q) (meaningNeg81 q) (meaning1630 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 1630 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1631 = true := by
  have hs : count1631 q = (countLit q [-75, -76]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-80, -81])
  have hm := merge_right (literal (valuationOf q) (1629)) (literal (valuationOf q) (1631)) (countLit q [-75, -76]) (countLit q [-80, -81]) (count1631 q) 1 (meaning1629 q) (meaning1631 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1631 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1632 = true := by
  have hs : count1631 q = (countLit q [-75, -76]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-80, -81])
  have hm := merge_right (literal (valuationOf q) (1630)) (literal (valuationOf q) (1632)) (countLit q [-75, -76]) (countLit q [-80, -81]) (count1631 q) 2 (meaning1630 q) (meaning1632 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1632 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1631 = true := by
  have hs : count1631 q = (countLit q [-75, -76]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-80, -81])
  have hm := merge_left (literal (valuationOf q) (1627)) (literal (valuationOf q) (1631)) (countLit q [-75, -76]) (countLit q [-80, -81]) (count1631 q) 1 (meaning1627 q) (meaning1631 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1631 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1632 = true := by
  have hs : count1631 q = (countLit q [-75, -76]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-80, -81])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1632)) (countLit q [-75, -76]) (countLit q [-80, -81]) (count1631 q) 1 1 (meaning1627 q) (meaning1629 q) (meaning1632 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1629 = false ∨ valuation q 1632 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1633 = true := by
  have hs : count1631 q = (countLit q [-75, -76]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-80, -81])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1633)) (countLit q [-75, -76]) (countLit q [-80, -81]) (count1631 q) 1 2 (meaning1627 q) (meaning1630 q) (meaning1633 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1630 = false ∨ valuation q 1633 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E019.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112019
