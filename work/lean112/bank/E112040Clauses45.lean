import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1709 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1709)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 4 3 (meaning1627 q) (meaning1689 q) (meaning1709 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1689 = false ∨ valuation q 1709 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1710 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1710)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 4 4 (meaning1627 q) (meaning1690 q) (meaning1710 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1690 = false ∨ valuation q 1710 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1711 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1711)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 4 5 (meaning1627 q) (meaning1691 q) (meaning1711 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1691 = false ∨ valuation q 1711 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1712 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1712)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 4 6 (meaning1627 q) (meaning1692 q) (meaning1712 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1692 = false ∨ valuation q 1712 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1713 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1713)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 4 7 (meaning1627 q) (meaning1693 q) (meaning1713 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1693 = false ∨ valuation q 1713 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1714 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1714)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 4 8 (meaning1627 q) (meaning1694 q) (meaning1714 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1694 = false ∨ valuation q 1714 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1715 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1715)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 4 9 (meaning1627 q) (meaning1695 q) (meaning1715 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1695 = false ∨ valuation q 1715 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1708 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1708)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 5 1 (meaning1628 q) (meaning1687 q) (meaning1708 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1687 = false ∨ valuation q 1708 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1709 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1709)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 5 2 (meaning1628 q) (meaning1688 q) (meaning1709 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1688 = false ∨ valuation q 1709 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1710 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1710)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 5 3 (meaning1628 q) (meaning1689 q) (meaning1710 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1689 = false ∨ valuation q 1710 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1711 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1711)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 5 4 (meaning1628 q) (meaning1690 q) (meaning1711 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1690 = false ∨ valuation q 1711 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1712 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1712)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 5 5 (meaning1628 q) (meaning1691 q) (meaning1712 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1691 = false ∨ valuation q 1712 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1713 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1713)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 5 6 (meaning1628 q) (meaning1692 q) (meaning1713 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1692 = false ∨ valuation q 1713 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1714 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1714)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 5 7 (meaning1628 q) (meaning1693 q) (meaning1714 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1693 = false ∨ valuation q 1714 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1715 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1715)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 5 8 (meaning1628 q) (meaning1694 q) (meaning1715 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1694 = false ∨ valuation q 1715 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1710 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1710)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 6 2 (meaning1629 q) (meaning1688 q) (meaning1710 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1688 = false ∨ valuation q 1710 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1711 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1711)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 6 3 (meaning1629 q) (meaning1689 q) (meaning1711 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1689 = false ∨ valuation q 1711 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1712 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1712)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 6 4 (meaning1629 q) (meaning1690 q) (meaning1712 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1690 = false ∨ valuation q 1712 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1713 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1713)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 6 5 (meaning1629 q) (meaning1691 q) (meaning1713 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1691 = false ∨ valuation q 1713 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1714 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1714)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 6 6 (meaning1629 q) (meaning1692 q) (meaning1714 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1692 = false ∨ valuation q 1714 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1712 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1712)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 7 3 (meaning1630 q) (meaning1689 q) (meaning1712 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1689 = false ∨ valuation q 1712 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1713 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1713)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 7 4 (meaning1630 q) (meaning1690 q) (meaning1713 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1690 = false ∨ valuation q 1713 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1714 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1714)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 7 5 (meaning1630 q) (meaning1691 q) (meaning1714 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1691 = false ∨ valuation q 1714 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1714 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1714)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 9 3 (meaning1632 q) (meaning1689 q) (meaning1714 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1689 = false ∨ valuation q 1714 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) + (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (l₂ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1724 q) 8 13 (meaning1566 q) (meaning1715 q) (meaning1744 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1715 = false ∨ valuation q 1744 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) + (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (l₂ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1724 q) 9 12 (meaning1567 q) (meaning1714 q) (meaning1744 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1714 = false ∨ valuation q 1744 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) + (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (l₂ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1724 q) 10 11 (meaning1568 q) (meaning1713 q) (meaning1744 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1713 = false ∨ valuation q 1744 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) + (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (l₂ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1712)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1724 q) 11 10 (meaning1569 q) (meaning1712 q) (meaning1744 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1712 = false ∨ valuation q 1744 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) + (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (l₂ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1711)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1724 q) 12 9 (meaning1570 q) (meaning1711 q) (meaning1744 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1711 = false ∨ valuation q 1744 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) + (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (l₂ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1724 q) 13 8 (meaning1571 q) (meaning1710 q) (meaning1744 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1710 = false ∨ valuation q 1744 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) + (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (l₂ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1724 q) 14 7 (meaning1572 q) (meaning1709 q) (meaning1744 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1709 = false ∨ valuation q 1744 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) + (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (l₂ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1724 q) 15 6 (meaning1573 q) (meaning1708 q) (meaning1744 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1708 = false ∨ valuation q 1744 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E040.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112040
