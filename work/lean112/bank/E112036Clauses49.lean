import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1569 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1853)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 7 6 (meaning1761 q) (meaning1829 q) (meaning1853 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1829 = false ∨ valuation q 1853 = true := counterClause1569 (baseVal q)

theorem counterClause1570 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1854)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 7 7 (meaning1761 q) (meaning1830 q) (meaning1854 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1570 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1830 = false ∨ valuation q 1854 = true := counterClause1570 (baseVal q)

theorem counterClause1571 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1855)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 7 8 (meaning1761 q) (meaning1831 q) (meaning1855 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1571 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1831 = false ∨ valuation q 1855 = true := counterClause1571 (baseVal q)

theorem counterClause1572 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1827)) (literal (valuationOf q) (1852)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 8 4 (meaning1762 q) (meaning1827 q) (meaning1852 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1572 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1827 = false ∨ valuation q 1852 = true := counterClause1572 (baseVal q)

theorem counterClause1573 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1853)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 8 5 (meaning1762 q) (meaning1828 q) (meaning1853 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1573 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1828 = false ∨ valuation q 1853 = true := counterClause1573 (baseVal q)

theorem counterClause1574 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1854)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 8 6 (meaning1762 q) (meaning1829 q) (meaning1854 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1574 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1829 = false ∨ valuation q 1854 = true := counterClause1574 (baseVal q)

theorem counterClause1575 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1855)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 8 7 (meaning1762 q) (meaning1830 q) (meaning1855 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1575 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1830 = false ∨ valuation q 1855 = true := counterClause1575 (baseVal q)

theorem counterClause1576 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1854)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 9 5 (meaning1763 q) (meaning1828 q) (meaning1854 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1576 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1828 = false ∨ valuation q 1854 = true := counterClause1576 (baseVal q)

theorem counterClause1577 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1855)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 9 6 (meaning1763 q) (meaning1829 q) (meaning1855 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1577 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1829 = false ∨ valuation q 1855 = true := counterClause1577 (baseVal q)

theorem counterClause1578 (q : Nat → Bool) : valuationOf q 1764 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1764)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1855)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 10 5 (meaning1764 q) (meaning1828 q) (meaning1855 q) hs
  change valuationOf q 1764 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1578 (q : Snake 81) (h : Conditions q) : valuation q 1764 = false ∨ valuation q 1828 = false ∨ valuation q 1855 = true := counterClause1578 (baseVal q)

theorem counterClause1579 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1855 = false ∨ valuationOf q 1892 = true := by
  have hs : count1867 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) + (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (l₂ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1691)) (literal (valuationOf q) (1855)) (literal (valuationOf q) (1892)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1867 q) 11 15 (meaning1691 q) (meaning1855 q) (meaning1892 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1855 = false ∨ valuationOf q 1892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1579 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1855 = false ∨ valuation q 1892 = true := counterClause1579 (baseVal q)

theorem counterClause1580 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1854 = false ∨ valuationOf q 1892 = true := by
  have hs : count1867 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) + (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (l₂ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1692)) (literal (valuationOf q) (1854)) (literal (valuationOf q) (1892)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1867 q) 12 14 (meaning1692 q) (meaning1854 q) (meaning1892 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1854 = false ∨ valuationOf q 1892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1580 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1854 = false ∨ valuation q 1892 = true := counterClause1580 (baseVal q)

theorem counterClause1581 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1853 = false ∨ valuationOf q 1892 = true := by
  have hs : count1867 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) + (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (l₂ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1853)) (literal (valuationOf q) (1892)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1867 q) 13 13 (meaning1693 q) (meaning1853 q) (meaning1892 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1853 = false ∨ valuationOf q 1892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1581 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1853 = false ∨ valuation q 1892 = true := counterClause1581 (baseVal q)

theorem counterClause1582 (q : Nat → Bool) : valuationOf q 1694 = false ∨ valuationOf q 1852 = false ∨ valuationOf q 1892 = true := by
  have hs : count1867 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) + (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (l₂ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1694)) (literal (valuationOf q) (1852)) (literal (valuationOf q) (1892)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1867 q) 14 12 (meaning1694 q) (meaning1852 q) (meaning1892 q) hs
  change valuationOf q 1694 = false ∨ valuationOf q 1852 = false ∨ valuationOf q 1892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1582 (q : Snake 81) (h : Conditions q) : valuation q 1694 = false ∨ valuation q 1852 = false ∨ valuation q 1892 = true := counterClause1582 (baseVal q)

theorem counterClause1583 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1851 = false ∨ valuationOf q 1892 = true := by
  have hs : count1867 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) + (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (l₂ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1695)) (literal (valuationOf q) (1851)) (literal (valuationOf q) (1892)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1867 q) 15 11 (meaning1695 q) (meaning1851 q) (meaning1892 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1851 = false ∨ valuationOf q 1892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1583 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1851 = false ∨ valuation q 1892 = true := counterClause1583 (baseVal q)

theorem counterClause1584 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1850 = false ∨ valuationOf q 1892 = true := by
  have hs : count1867 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) + (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (l₂ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1850)) (literal (valuationOf q) (1892)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1867 q) 16 10 (meaning1696 q) (meaning1850 q) (meaning1892 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1850 = false ∨ valuationOf q 1892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1584 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1850 = false ∨ valuation q 1892 = true := counterClause1584 (baseVal q)

theorem counterClause1585 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1849 = false ∨ valuationOf q 1892 = true := by
  have hs : count1867 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) + (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (l₂ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1849)) (literal (valuationOf q) (1892)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28, -32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93, -96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1867 q) 17 9 (meaning1697 q) (meaning1849 q) (meaning1892 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1849 = false ∨ valuationOf q 1892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1585 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1849 = false ∨ valuation q 1892 = true := counterClause1585 (baseVal q)

theorem clause1586 (q : Snake 81) (h : Conditions q) : valuation q 1892 = false := by
  rw [value1892]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1867 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1587 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 11 = false ∨ valuation q 12 = false := by
  rw [value3, value4, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (36 : Vertex) (37 : Vertex) (52 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1588 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 12 = false ∨ valuation q 13 = false := by
  rw [value4, value5, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (37 : Vertex) (39 : Vertex) (53 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1589 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 10 = false := by
  rw [value6, value8, value9, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (40 : Vertex) (42 : Vertex) (44 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1590 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 37 = false ∨ valuation q 73 = false ∨ valuation q 95 = false := by
  rw [value6, value37, value73, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (40 : Vertex) (168 : Vertex) (296 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1591 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 34 = false := by
  rw [value31, value32, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1592 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value31, value32, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1593 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 37 = false ∨ valuation q 41 = false ∨ valuation q 46 = false := by
  rw [value31, value37, value41, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (176 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1594 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 37 = false ∨ valuation q 88 = false ∨ valuation q 95 = false := by
  rw [value31, value37, value88, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (416 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1595 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 42 = false ∨ valuation q 44 = false := by
  rw [value32, value34, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (163 : Vertex) (177 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1596 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 35 = false ∨ valuation q 89 = false ∨ valuation q 92 = false := by
  rw [value32, value35, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (165 : Vertex) (417 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1597 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 42 = false ∨ valuation q 89 = false ∨ valuation q 101 = false := by
  rw [value32, value42, value89, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (177 : Vertex) (417 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1598 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value33, value36, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (162 : Vertex) (166 : Vertex) (178 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1599 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 46 = false ∨ valuation q 95 = false ∨ valuation q 106 = false := by
  rw [value37, value46, value95, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (168 : Vertex) (184 : Vertex) (424 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1600 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value38, value40, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (171 : Vertex) (175 : Vertex) (427 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E036.Block49 (valuation q) :=
  ⟨clause1569 q h, clause1570 q h, clause1571 q h, clause1572 q h, clause1573 q h, clause1574 q h, clause1575 q h, clause1576 q h, clause1577 q h, clause1578 q h, clause1579 q h, clause1580 q h, clause1581 q h, clause1582 q h, clause1583 q h, clause1584 q h, clause1585 q h, clause1586 q h, clause1587 q h, clause1588 q h, clause1589 q h, clause1590 q h, clause1591 q h, clause1592 q h, clause1593 q h, clause1594 q h, clause1595 q h, clause1596 q h, clause1597 q h, clause1598 q h, clause1599 q h, clause1600 q h⟩

end
end Snake9.Regrowth.E112036
