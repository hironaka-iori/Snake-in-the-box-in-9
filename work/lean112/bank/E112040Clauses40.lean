import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-82, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -88])
  have hm := merge_left (literal (valuationOf q) (1608)) (literal (valuationOf q) (1612)) (countLit q [-82, -85]) (countLit q [-87, -88]) (count1612 q) 1 (meaning1608 q) (meaning1612 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1612 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-82, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1613)) (countLit q [-82, -85]) (countLit q [-87, -88]) (count1612 q) 1 1 (meaning1608 q) (meaning1610 q) (meaning1613 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1610 = false ∨ valuation q 1613 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-82, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1614)) (countLit q [-82, -85]) (countLit q [-87, -88]) (count1612 q) 1 2 (meaning1608 q) (meaning1611 q) (meaning1614 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1611 = false ∨ valuation q 1614 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-82, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -88])
  have hm := merge_left (literal (valuationOf q) (1609)) (literal (valuationOf q) (1613)) (countLit q [-82, -85]) (countLit q [-87, -88]) (count1612 q) 2 (meaning1609 q) (meaning1613 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1613 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-82, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1614)) (countLit q [-82, -85]) (countLit q [-87, -88]) (count1612 q) 2 1 (meaning1609 q) (meaning1610 q) (meaning1614 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1610 = false ∨ valuation q 1614 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -80]) (l₂ := [-82, -85, -87, -88])
  have hm := merge_left (literal (valuationOf q) (1604)) (literal (valuationOf q) (1616)) (countLit q [-76, -77, -79, -80]) (countLit q [-82, -85, -87, -88]) (count1616 q) 1 (meaning1604 q) (meaning1616 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1616 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -80]) (l₂ := [-82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1617)) (countLit q [-76, -77, -79, -80]) (countLit q [-82, -85, -87, -88]) (count1616 q) 1 1 (meaning1604 q) (meaning1612 q) (meaning1617 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1612 = false ∨ valuation q 1617 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -80]) (l₂ := [-82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1618)) (countLit q [-76, -77, -79, -80]) (countLit q [-82, -85, -87, -88]) (count1616 q) 1 2 (meaning1604 q) (meaning1613 q) (meaning1618 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1613 = false ∨ valuation q 1618 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -80]) (l₂ := [-82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1619)) (countLit q [-76, -77, -79, -80]) (countLit q [-82, -85, -87, -88]) (count1616 q) 1 3 (meaning1604 q) (meaning1614 q) (meaning1619 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1614 = false ∨ valuation q 1619 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -80]) (l₂ := [-82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1618)) (countLit q [-76, -77, -79, -80]) (countLit q [-82, -85, -87, -88]) (count1616 q) 2 1 (meaning1605 q) (meaning1612 q) (meaning1618 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1612 = false ∨ valuation q 1618 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -80]) (l₂ := [-82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1619)) (countLit q [-76, -77, -79, -80]) (countLit q [-82, -85, -87, -88]) (count1616 q) 2 2 (meaning1605 q) (meaning1613 q) (meaning1619 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1613 = false ∨ valuation q 1619 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1620 = true := by
  have hs : count1616 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -80]) (l₂ := [-82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1620)) (countLit q [-76, -77, -79, -80]) (countLit q [-82, -85, -87, -88]) (count1616 q) 2 3 (meaning1605 q) (meaning1614 q) (meaning1620 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1614 = false ∨ valuation q 1620 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -80]) (l₂ := [-82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1619)) (countLit q [-76, -77, -79, -80]) (countLit q [-82, -85, -87, -88]) (count1616 q) 3 1 (meaning1606 q) (meaning1612 q) (meaning1619 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1612 = false ∨ valuation q 1619 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1620 = true := by
  have hs : count1616 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -80]) (l₂ := [-82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1620)) (countLit q [-76, -77, -79, -80]) (countLit q [-82, -85, -87, -88]) (count1616 q) 3 2 (meaning1606 q) (meaning1613 q) (meaning1620 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1613 = false ∨ valuation q 1620 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1625 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1625)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 1 1 (meaning1593 q) (meaning1616 q) (meaning1625 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1616 = false ∨ valuation q 1625 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1626 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1626)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 1 2 (meaning1593 q) (meaning1617 q) (meaning1626 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1617 = false ∨ valuation q 1626 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1627 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1627)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 1 3 (meaning1593 q) (meaning1618 q) (meaning1627 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1618 = false ∨ valuation q 1627 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1628)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 1 4 (meaning1593 q) (meaning1619 q) (meaning1628 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1619 = false ∨ valuation q 1628 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1629)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 1 5 (meaning1593 q) (meaning1620 q) (meaning1629 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1620 = false ∨ valuation q 1629 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1627 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1627)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 2 2 (meaning1594 q) (meaning1617 q) (meaning1627 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1617 = false ∨ valuation q 1627 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1628)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 2 3 (meaning1594 q) (meaning1618 q) (meaning1628 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1618 = false ∨ valuation q 1628 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1629)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 2 4 (meaning1594 q) (meaning1619 q) (meaning1629 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1619 = false ∨ valuation q 1629 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1630 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1630)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 2 5 (meaning1594 q) (meaning1620 q) (meaning1630 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1620 = false ∨ valuation q 1630 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1628)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 3 2 (meaning1595 q) (meaning1617 q) (meaning1628 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1617 = false ∨ valuation q 1628 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1629)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 3 3 (meaning1595 q) (meaning1618 q) (meaning1629 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1618 = false ∨ valuation q 1629 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1630 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1630)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 3 4 (meaning1595 q) (meaning1619 q) (meaning1630 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1619 = false ∨ valuation q 1630 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1628)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 4 1 (meaning1596 q) (meaning1616 q) (meaning1628 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1616 = false ∨ valuation q 1628 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1629)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 4 2 (meaning1596 q) (meaning1617 q) (meaning1629 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1617 = false ∨ valuation q 1629 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1630 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1630)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 4 3 (meaning1596 q) (meaning1618 q) (meaning1630 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1618 = false ∨ valuation q 1630 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1632 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -63, -64, -70, -71, -73]) + (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73]) (l₂ := [-76, -77, -79, -80, -82, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1632)) (countLit q [-61, -62, -63, -64, -70, -71, -73]) (countLit q [-76, -77, -79, -80, -82, -85, -87, -88]) (count1624 q) 7 2 (meaning1599 q) (meaning1617 q) (meaning1632 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1617 = false ∨ valuation q 1632 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-90]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92])
  have hm := merge_right (literal (valuationOf q) (-92)) (literal (valuationOf q) (1639)) (countLit q [-90]) (countLit q [-92]) (count1639 q) 1 (meaningNeg92 q) (meaning1639 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1639 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-90]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1639)) (countLit q [-90]) (countLit q [-92]) (count1639 q) 1 (meaningNeg90 q) (meaning1639 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1639 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E040.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112040
