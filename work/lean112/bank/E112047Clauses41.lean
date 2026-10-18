import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1613 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1613)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 1 4 (meaning1582 q) (meaning1605 q) (meaning1613 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1605 = false ∨ valuation q 1613 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1614 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1614)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 1 5 (meaning1582 q) (meaning1606 q) (meaning1614 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1606 = false ∨ valuation q 1614 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1615 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1615)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 1 6 (meaning1582 q) (meaning1607 q) (meaning1615 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1607 = false ∨ valuation q 1615 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1611 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1611)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 2 1 (meaning1583 q) (meaning1602 q) (meaning1611 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1602 = false ∨ valuation q 1611 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1612 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1612)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 2 2 (meaning1583 q) (meaning1603 q) (meaning1612 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1603 = false ∨ valuation q 1612 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1613 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1613)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 2 3 (meaning1583 q) (meaning1604 q) (meaning1613 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1604 = false ∨ valuation q 1613 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1614 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1614)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 2 4 (meaning1583 q) (meaning1605 q) (meaning1614 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1605 = false ∨ valuation q 1614 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1615 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1615)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 2 5 (meaning1583 q) (meaning1606 q) (meaning1615 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1606 = false ∨ valuation q 1615 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1616 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1616)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 2 6 (meaning1583 q) (meaning1607 q) (meaning1616 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1607 = false ∨ valuation q 1616 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1611 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1584)) (literal (valuationOf q) (1611)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 3 (meaning1584 q) (meaning1611 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1611 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1612 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1612)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 3 1 (meaning1584 q) (meaning1602 q) (meaning1612 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1602 = false ∨ valuation q 1612 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1613 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1613)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 3 2 (meaning1584 q) (meaning1603 q) (meaning1613 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1603 = false ∨ valuation q 1613 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1614 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1614)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 3 3 (meaning1584 q) (meaning1604 q) (meaning1614 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1604 = false ∨ valuation q 1614 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1615 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1615)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 3 4 (meaning1584 q) (meaning1605 q) (meaning1615 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1605 = false ∨ valuation q 1615 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1616 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1616)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 3 5 (meaning1584 q) (meaning1606 q) (meaning1616 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1606 = false ∨ valuation q 1616 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1612 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1585)) (literal (valuationOf q) (1612)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 4 (meaning1585 q) (meaning1612 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1612 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1613 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1613)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 4 1 (meaning1585 q) (meaning1602 q) (meaning1613 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1602 = false ∨ valuation q 1613 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1614 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1614)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 4 2 (meaning1585 q) (meaning1603 q) (meaning1614 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1603 = false ∨ valuation q 1614 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1615 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1615)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 4 3 (meaning1585 q) (meaning1604 q) (meaning1615 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1604 = false ∨ valuation q 1615 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1616 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1616)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 4 4 (meaning1585 q) (meaning1605 q) (meaning1616 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1605 = false ∨ valuation q 1616 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1613 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1586)) (literal (valuationOf q) (1613)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 5 (meaning1586 q) (meaning1613 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1613 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1614 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1614)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 5 1 (meaning1586 q) (meaning1602 q) (meaning1614 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1602 = false ∨ valuation q 1614 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1615 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1615)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 5 2 (meaning1586 q) (meaning1603 q) (meaning1615 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1603 = false ∨ valuation q 1615 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1616 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1616)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 5 3 (meaning1586 q) (meaning1604 q) (meaning1616 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1604 = false ∨ valuation q 1616 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1617 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1617)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 5 4 (meaning1586 q) (meaning1605 q) (meaning1617 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1605 = false ∨ valuation q 1617 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1615 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1615)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 6 1 (meaning1587 q) (meaning1602 q) (meaning1615 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1602 = false ∨ valuation q 1615 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1616 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1616)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 6 2 (meaning1587 q) (meaning1603 q) (meaning1616 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1603 = false ∨ valuation q 1616 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1617 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1617)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 6 3 (meaning1587 q) (meaning1604 q) (meaning1617 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1604 = false ∨ valuation q 1617 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-93]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1623)) (countLit q [-93]) (countLit q [-96]) (count1623 q) 1 (meaningNeg96 q) (meaning1623 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1623 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-93]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1623)) (countLit q [-93]) (countLit q [-96]) (count1623 q) 1 (meaningNeg93 q) (meaning1623 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1623 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-93]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1624)) (countLit q [-93]) (countLit q [-96]) (count1623 q) 1 1 (meaningNeg93 q) (meaningNeg96 q) (meaning1624 q) hs
  change (! (valuationOf q 93)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 96 = true ∨ valuation q 1624 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-92]) + (countLit q [-93, -96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -96])
  have hm := merge_right (literal (valuationOf q) (1623)) (literal (valuationOf q) (1625)) (countLit q [-92]) (countLit q [-93, -96]) (count1625 q) 1 (meaning1623 q) (meaning1625 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1625 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E047.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112047
