import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec52 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1665 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1717 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1633)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1717)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 10 5 (meaning1633 q) (meaning1691 q) (meaning1717 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1665 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1691 = false ∨ valuation q 1717 = true := counterClause1665 (baseVal q)

theorem counterClause1666 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1744)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1724 q) 6 15 (meaning1564 q) (meaning1717 q) (meaning1744 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1666 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1717 = false ∨ valuation q 1744 = true := counterClause1666 (baseVal q)

theorem counterClause1667 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1744)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1724 q) 7 14 (meaning1565 q) (meaning1716 q) (meaning1744 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1667 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1716 = false ∨ valuation q 1744 = true := counterClause1667 (baseVal q)

theorem counterClause1668 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1744)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1724 q) 8 13 (meaning1566 q) (meaning1715 q) (meaning1744 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1668 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1715 = false ∨ valuation q 1744 = true := counterClause1668 (baseVal q)

theorem counterClause1669 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1744)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1724 q) 9 12 (meaning1567 q) (meaning1714 q) (meaning1744 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1669 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1714 = false ∨ valuation q 1744 = true := counterClause1669 (baseVal q)

theorem counterClause1670 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1744)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1724 q) 10 11 (meaning1568 q) (meaning1713 q) (meaning1744 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1670 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1713 = false ∨ valuation q 1744 = true := counterClause1670 (baseVal q)

theorem counterClause1671 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1712)) (literal (valuationOf q) (1744)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1724 q) 11 10 (meaning1569 q) (meaning1712 q) (meaning1744 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1671 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1712 = false ∨ valuation q 1744 = true := counterClause1671 (baseVal q)

theorem counterClause1672 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1711)) (literal (valuationOf q) (1744)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1724 q) 12 9 (meaning1570 q) (meaning1711 q) (meaning1744 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1672 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1711 = false ∨ valuation q 1744 = true := counterClause1672 (baseVal q)

theorem counterClause1673 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1744)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1724 q) 13 8 (meaning1571 q) (meaning1710 q) (meaning1744 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1673 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1710 = false ∨ valuation q 1744 = true := counterClause1673 (baseVal q)

theorem counterClause1674 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1744)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1724 q) 14 7 (meaning1572 q) (meaning1709 q) (meaning1744 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1674 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1709 = false ∨ valuation q 1744 = true := counterClause1674 (baseVal q)

theorem counterClause1675 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1744)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1724 q) 15 6 (meaning1573 q) (meaning1708 q) (meaning1744 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1675 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1708 = false ∨ valuation q 1744 = true := counterClause1675 (baseVal q)

theorem counterClause1676 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1744)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30, -32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87, -90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1724 q) 16 5 (meaning1574 q) (meaning1707 q) (meaning1744 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1676 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1707 = false ∨ valuation q 1744 = true := counterClause1676 (baseVal q)

theorem clause1677 (q : Snake 81) (h : Conditions q) : valuation q 1744 = false := by
  rw [value1744]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1724 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1678 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false := by
  rw [value4, value5, value6, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (40 : Vertex) (41 : Vertex) (42 : Vertex) (43 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1679 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value4, value5, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (40 : Vertex) (41 : Vertex) (56 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1680 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value5, value7, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (41 : Vertex) (43 : Vertex) (169 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1681 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 14 = false ∨ valuation q 39 = false ∨ valuation q 51 = false := by
  rw [value5, value14, value39, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (41 : Vertex) (57 : Vertex) (169 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1682 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 24 = false ∨ valuation q 29 = false := by
  rw [value9, value13, value24, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (48 : Vertex) (56 : Vertex) (112 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1683 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 44 = false ∨ valuation q 50 = false := by
  rw [value9, value13, value44, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (48 : Vertex) (56 : Vertex) (176 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1684 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value13, value14, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (56 : Vertex) (57 : Vertex) (184 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1685 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 29 = false ∨ valuation q 50 = false ∨ valuation q 71 = false := by
  rw [value13, value29, value50, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (56 : Vertex) (120 : Vertex) (184 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1686 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 29 = false ∨ valuation q 79 = false ∨ valuation q 82 = false := by
  rw [value21, value29, value79, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (104 : Vertex) (120 : Vertex) (360 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1687 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 27 = false ∨ valuation q 28 = false := by
  rw [value24, value25, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (112 : Vertex) (114 : Vertex) (116 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1688 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 29 = false ∨ valuation q 66 = false ∨ valuation q 71 = false := by
  rw [value24, value29, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (112 : Vertex) (120 : Vertex) (240 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1689 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value25, value26, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (114 : Vertex) (115 : Vertex) (122 : Vertex) (123 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1690 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value34, value35, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1691 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 45 = false ∨ valuation q 46 = false := by
  rw [value36, value37, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (162 : Vertex) (163 : Vertex) (178 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1692 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 43 = false := by
  rw [value37, value38, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (163 : Vertex) (167 : Vertex) (171 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1693 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 46 = false ∨ valuation q 49 = false := by
  rw [value37, value38, value46, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (163 : Vertex) (167 : Vertex) (179 : Vertex) (183 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1694 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 43 = false ∨ valuation q 49 = false ∨ valuation q 56 = false := by
  rw [value38, value43, value49, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (167 : Vertex) (175 : Vertex) (183 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1695 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 49 = false ∨ valuation q 88 = false ∨ valuation q 97 = false := by
  rw [value38, value49, value88, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (167 : Vertex) (183 : Vertex) (423 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1696 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value39, value40, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (169 : Vertex) (171 : Vertex) (173 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block52 (q : Snake 81) (h : Conditions q) : B112E004.Block52 (valuation q) :=
  ⟨clause1665 q h, clause1666 q h, clause1667 q h, clause1668 q h, clause1669 q h, clause1670 q h, clause1671 q h, clause1672 q h, clause1673 q h, clause1674 q h, clause1675 q h, clause1676 q h, clause1677 q h, clause1678 q h, clause1679 q h, clause1680 q h, clause1681 q h, clause1682 q h, clause1683 q h, clause1684 q h, clause1685 q h, clause1686 q h, clause1687 q h, clause1688 q h, clause1689 q h, clause1690 q h, clause1691 q h, clause1692 q h, clause1693 q h, clause1694 q h, clause1695 q h, clause1696 q h⟩

end
end Snake9.Regrowth.E112004
