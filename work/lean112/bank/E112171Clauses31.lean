import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1589 = true := by
  have hs : count1588 q = (countLit q [-86, -88, -89, -93, -94, -95, -96]) + (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89, -93, -94, -95, -96]) (l₂ := [-100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1589)) (countLit q [-86, -88, -89, -93, -94, -95, -96]) (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) (count1588 q) 1 1 (meaning1557 q) (meaning1580 q) (meaning1589 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1580 = false ∨ valuation q 1589 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1590 = true := by
  have hs : count1588 q = (countLit q [-86, -88, -89, -93, -94, -95, -96]) + (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89, -93, -94, -95, -96]) (l₂ := [-100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1590)) (countLit q [-86, -88, -89, -93, -94, -95, -96]) (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) (count1588 q) 1 2 (meaning1557 q) (meaning1581 q) (meaning1590 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1581 = false ∨ valuation q 1590 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1591 = true := by
  have hs : count1588 q = (countLit q [-86, -88, -89, -93, -94, -95, -96]) + (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89, -93, -94, -95, -96]) (l₂ := [-100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1591)) (countLit q [-86, -88, -89, -93, -94, -95, -96]) (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) (count1588 q) 1 3 (meaning1557 q) (meaning1582 q) (meaning1591 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1582 = false ∨ valuation q 1591 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1590 = true := by
  have hs : count1588 q = (countLit q [-86, -88, -89, -93, -94, -95, -96]) + (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89, -93, -94, -95, -96]) (l₂ := [-100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1590)) (countLit q [-86, -88, -89, -93, -94, -95, -96]) (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) (count1588 q) 2 1 (meaning1558 q) (meaning1580 q) (meaning1590 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1580 = false ∨ valuation q 1590 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1591 = true := by
  have hs : count1588 q = (countLit q [-86, -88, -89, -93, -94, -95, -96]) + (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89, -93, -94, -95, -96]) (l₂ := [-100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1591)) (countLit q [-86, -88, -89, -93, -94, -95, -96]) (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) (count1588 q) 2 2 (meaning1558 q) (meaning1581 q) (meaning1591 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1581 = false ∨ valuation q 1591 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1592 = true := by
  have hs : count1588 q = (countLit q [-86, -88, -89, -93, -94, -95, -96]) + (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89, -93, -94, -95, -96]) (l₂ := [-100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1592)) (countLit q [-86, -88, -89, -93, -94, -95, -96]) (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) (count1588 q) 2 3 (meaning1558 q) (meaning1582 q) (meaning1592 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1582 = false ∨ valuation q 1592 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1590 = true := by
  have hs : count1588 q = (countLit q [-86, -88, -89, -93, -94, -95, -96]) + (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89, -93, -94, -95, -96]) (l₂ := [-100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_left (literal (valuationOf q) (1559)) (literal (valuationOf q) (1590)) (countLit q [-86, -88, -89, -93, -94, -95, -96]) (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) (count1588 q) 3 (meaning1559 q) (meaning1590 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1590 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1591 = true := by
  have hs : count1588 q = (countLit q [-86, -88, -89, -93, -94, -95, -96]) + (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89, -93, -94, -95, -96]) (l₂ := [-100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1591)) (countLit q [-86, -88, -89, -93, -94, -95, -96]) (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) (count1588 q) 3 1 (meaning1559 q) (meaning1580 q) (meaning1591 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1580 = false ∨ valuation q 1591 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1592 = true := by
  have hs : count1588 q = (countLit q [-86, -88, -89, -93, -94, -95, -96]) + (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89, -93, -94, -95, -96]) (l₂ := [-100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1592)) (countLit q [-86, -88, -89, -93, -94, -95, -96]) (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) (count1588 q) 3 2 (meaning1559 q) (meaning1581 q) (meaning1592 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1581 = false ∨ valuation q 1592 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1593 = true := by
  have hs : count1588 q = (countLit q [-86, -88, -89, -93, -94, -95, -96]) + (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89, -93, -94, -95, -96]) (l₂ := [-100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1593)) (countLit q [-86, -88, -89, -93, -94, -95, -96]) (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) (count1588 q) 3 3 (meaning1559 q) (meaning1582 q) (meaning1593 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1582 = false ∨ valuation q 1593 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1592 = true := by
  have hs : count1588 q = (countLit q [-86, -88, -89, -93, -94, -95, -96]) + (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89, -93, -94, -95, -96]) (l₂ := [-100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1592)) (countLit q [-86, -88, -89, -93, -94, -95, -96]) (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) (count1588 q) 4 1 (meaning1560 q) (meaning1580 q) (meaning1592 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1580 = false ∨ valuation q 1592 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1607 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1607)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 2 3 (meaning1531 q) (meaning1590 q) (meaning1607 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1590 = false ∨ valuation q 1607 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1608 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1608)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 2 4 (meaning1531 q) (meaning1591 q) (meaning1608 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1591 = false ∨ valuation q 1608 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1609 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1609)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 2 5 (meaning1531 q) (meaning1592 q) (meaning1609 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1592 = false ∨ valuation q 1609 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1610 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1610)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 2 6 (meaning1531 q) (meaning1593 q) (meaning1610 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1593 = false ∨ valuation q 1610 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1607 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1607)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 3 2 (meaning1532 q) (meaning1589 q) (meaning1607 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1589 = false ∨ valuation q 1607 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1608 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1608)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 3 3 (meaning1532 q) (meaning1590 q) (meaning1608 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1590 = false ∨ valuation q 1608 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1609 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1609)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 3 4 (meaning1532 q) (meaning1591 q) (meaning1609 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1591 = false ∨ valuation q 1609 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1610 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1610)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 3 5 (meaning1532 q) (meaning1592 q) (meaning1610 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1592 = false ∨ valuation q 1610 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1611 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1611)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 3 6 (meaning1532 q) (meaning1593 q) (meaning1611 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1593 = false ∨ valuation q 1611 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1608 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1608)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 4 2 (meaning1533 q) (meaning1589 q) (meaning1608 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1589 = false ∨ valuation q 1608 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1609 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1609)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 4 3 (meaning1533 q) (meaning1590 q) (meaning1609 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1590 = false ∨ valuation q 1609 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1610 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1610)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 4 4 (meaning1533 q) (meaning1591 q) (meaning1610 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1591 = false ∨ valuation q 1610 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1611 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1611)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 4 5 (meaning1533 q) (meaning1592 q) (meaning1611 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1592 = false ∨ valuation q 1611 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1612 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1612)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 4 6 (meaning1533 q) (meaning1593 q) (meaning1612 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1593 = false ∨ valuation q 1612 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1609 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1609)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 5 2 (meaning1534 q) (meaning1589 q) (meaning1609 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1589 = false ∨ valuation q 1609 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1610 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1610)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 5 3 (meaning1534 q) (meaning1590 q) (meaning1610 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1590 = false ∨ valuation q 1610 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1611 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1611)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 5 4 (meaning1534 q) (meaning1591 q) (meaning1611 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1591 = false ∨ valuation q 1611 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1612 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1612)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 5 5 (meaning1534 q) (meaning1592 q) (meaning1612 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1592 = false ∨ valuation q 1612 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1610 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1610)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 6 2 (meaning1535 q) (meaning1589 q) (meaning1610 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1589 = false ∨ valuation q 1610 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1611 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1611)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 6 3 (meaning1535 q) (meaning1590 q) (meaning1611 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1590 = false ∨ valuation q 1611 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1612 = true := by
  have hs : count1603 q = (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) + (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (l₂ := [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1612)) (countLit q [-58, -60, -63, -66, -68, -69, -71, -72, -76, -77, -78, -79, -83, -85]) (countLit q [-86, -88, -89, -93, -94, -95, -96, -100, -102, -103, -105, -109, -110, -111, -112]) (count1603 q) 6 4 (meaning1535 q) (meaning1591 q) (meaning1612 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1591 = false ∨ valuation q 1612 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E171.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112171
