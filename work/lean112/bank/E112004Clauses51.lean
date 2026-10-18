import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec51 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1633 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1710 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1710)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 3 5 (meaning1626 q) (meaning1691 q) (meaning1710 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1633 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1691 = false ∨ valuation q 1710 = true := counterClause1633 (baseVal q)

theorem counterClause1634 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1711 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1711)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 3 6 (meaning1626 q) (meaning1692 q) (meaning1711 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1634 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1692 = false ∨ valuation q 1711 = true := counterClause1634 (baseVal q)

theorem counterClause1635 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1712 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1712)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 3 7 (meaning1626 q) (meaning1693 q) (meaning1712 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1635 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1693 = false ∨ valuation q 1712 = true := counterClause1635 (baseVal q)

theorem counterClause1636 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1713 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1713)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 3 8 (meaning1626 q) (meaning1694 q) (meaning1713 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1636 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1694 = false ∨ valuation q 1713 = true := counterClause1636 (baseVal q)

theorem counterClause1637 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1714 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1714)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 3 9 (meaning1626 q) (meaning1695 q) (meaning1714 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1637 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1695 = false ∨ valuation q 1714 = true := counterClause1637 (baseVal q)

theorem counterClause1638 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1710 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1710)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 4 4 (meaning1627 q) (meaning1690 q) (meaning1710 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1638 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1690 = false ∨ valuation q 1710 = true := counterClause1638 (baseVal q)

theorem counterClause1639 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1711 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1711)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 4 5 (meaning1627 q) (meaning1691 q) (meaning1711 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1639 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1691 = false ∨ valuation q 1711 = true := counterClause1639 (baseVal q)

theorem counterClause1640 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1712 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1712)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 4 6 (meaning1627 q) (meaning1692 q) (meaning1712 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1640 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1692 = false ∨ valuation q 1712 = true := counterClause1640 (baseVal q)

theorem counterClause1641 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1713 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1713)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 4 7 (meaning1627 q) (meaning1693 q) (meaning1713 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1641 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1693 = false ∨ valuation q 1713 = true := counterClause1641 (baseVal q)

theorem counterClause1642 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1714 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1714)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 4 8 (meaning1627 q) (meaning1694 q) (meaning1714 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1642 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1694 = false ∨ valuation q 1714 = true := counterClause1642 (baseVal q)

theorem counterClause1643 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1715 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1715)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 4 9 (meaning1627 q) (meaning1695 q) (meaning1715 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1643 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1695 = false ∨ valuation q 1715 = true := counterClause1643 (baseVal q)

theorem counterClause1644 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1711 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1711)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 5 4 (meaning1628 q) (meaning1690 q) (meaning1711 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1644 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1690 = false ∨ valuation q 1711 = true := counterClause1644 (baseVal q)

theorem counterClause1645 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1712 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1712)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 5 5 (meaning1628 q) (meaning1691 q) (meaning1712 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1645 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1691 = false ∨ valuation q 1712 = true := counterClause1645 (baseVal q)

theorem counterClause1646 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1713 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1713)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 5 6 (meaning1628 q) (meaning1692 q) (meaning1713 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1646 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1692 = false ∨ valuation q 1713 = true := counterClause1646 (baseVal q)

theorem counterClause1647 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1714 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1714)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 5 7 (meaning1628 q) (meaning1693 q) (meaning1714 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1647 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1693 = false ∨ valuation q 1714 = true := counterClause1647 (baseVal q)

theorem counterClause1648 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1715 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1715)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 5 8 (meaning1628 q) (meaning1694 q) (meaning1715 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1648 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1694 = false ∨ valuation q 1715 = true := counterClause1648 (baseVal q)

theorem counterClause1649 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1711 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1711)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 6 3 (meaning1629 q) (meaning1689 q) (meaning1711 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1649 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1689 = false ∨ valuation q 1711 = true := counterClause1649 (baseVal q)

theorem counterClause1650 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1712 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1712)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 6 4 (meaning1629 q) (meaning1690 q) (meaning1712 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1650 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1690 = false ∨ valuation q 1712 = true := counterClause1650 (baseVal q)

theorem counterClause1651 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1713 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1713)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 6 5 (meaning1629 q) (meaning1691 q) (meaning1713 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1651 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1691 = false ∨ valuation q 1713 = true := counterClause1651 (baseVal q)

theorem counterClause1652 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1714 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1714)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 6 6 (meaning1629 q) (meaning1692 q) (meaning1714 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1652 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1692 = false ∨ valuation q 1714 = true := counterClause1652 (baseVal q)

theorem counterClause1653 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1715 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1715)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 6 7 (meaning1629 q) (meaning1693 q) (meaning1715 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1653 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1693 = false ∨ valuation q 1715 = true := counterClause1653 (baseVal q)

theorem counterClause1654 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1713 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1713)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 7 4 (meaning1630 q) (meaning1690 q) (meaning1713 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1654 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1690 = false ∨ valuation q 1713 = true := counterClause1654 (baseVal q)

theorem counterClause1655 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1714 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1714)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 7 5 (meaning1630 q) (meaning1691 q) (meaning1714 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1655 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1691 = false ∨ valuation q 1714 = true := counterClause1655 (baseVal q)

theorem counterClause1656 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1715 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1715)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 7 6 (meaning1630 q) (meaning1692 q) (meaning1715 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1656 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1692 = false ∨ valuation q 1715 = true := counterClause1656 (baseVal q)

theorem counterClause1657 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1716 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1716)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 7 7 (meaning1630 q) (meaning1693 q) (meaning1716 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1657 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1693 = false ∨ valuation q 1716 = true := counterClause1657 (baseVal q)

theorem counterClause1658 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1713 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1713)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 8 3 (meaning1631 q) (meaning1689 q) (meaning1713 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1658 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1689 = false ∨ valuation q 1713 = true := counterClause1658 (baseVal q)

theorem counterClause1659 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1714 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1714)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 8 4 (meaning1631 q) (meaning1690 q) (meaning1714 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1659 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1690 = false ∨ valuation q 1714 = true := counterClause1659 (baseVal q)

theorem counterClause1660 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1715 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1715)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 8 5 (meaning1631 q) (meaning1691 q) (meaning1715 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1660 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1691 = false ∨ valuation q 1715 = true := counterClause1660 (baseVal q)

theorem counterClause1661 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1716 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1716)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 8 6 (meaning1631 q) (meaning1692 q) (meaning1716 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1661 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1692 = false ∨ valuation q 1716 = true := counterClause1661 (baseVal q)

theorem counterClause1662 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1717 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1717)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 8 7 (meaning1631 q) (meaning1693 q) (meaning1717 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1662 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1693 = false ∨ valuation q 1717 = true := counterClause1662 (baseVal q)

theorem counterClause1663 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1715 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1715)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 9 4 (meaning1632 q) (meaning1690 q) (meaning1715 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1663 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1690 = false ∨ valuation q 1715 = true := counterClause1663 (baseVal q)

theorem counterClause1664 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1716 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1716)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 9 5 (meaning1632 q) (meaning1691 q) (meaning1716 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1664 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1691 = false ∨ valuation q 1716 = true := counterClause1664 (baseVal q)

theorem block51 (q : Snake 81) (h : Conditions q) : B112E004.Block51 (valuation q) :=
  ⟨clause1633 q h, clause1634 q h, clause1635 q h, clause1636 q h, clause1637 q h, clause1638 q h, clause1639 q h, clause1640 q h, clause1641 q h, clause1642 q h, clause1643 q h, clause1644 q h, clause1645 q h, clause1646 q h, clause1647 q h, clause1648 q h, clause1649 q h, clause1650 q h, clause1651 q h, clause1652 q h, clause1653 q h, clause1654 q h, clause1655 q h, clause1656 q h, clause1657 q h, clause1658 q h, clause1659 q h, clause1660 q h, clause1661 q h, clause1662 q h, clause1663 q h, clause1664 q h⟩

end
end Snake9.Regrowth.E112004
