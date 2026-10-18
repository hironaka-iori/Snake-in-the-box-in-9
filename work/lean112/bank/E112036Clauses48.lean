import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1850 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1756)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1850)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 2 8 (meaning1756 q) (meaning1831 q) (meaning1850 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1831 = false ∨ valuation q 1850 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1851 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1756)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1851)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 2 9 (meaning1756 q) (meaning1832 q) (meaning1851 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1832 = false ∨ valuation q 1851 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1756)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1852)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 2 10 (meaning1756 q) (meaning1833 q) (meaning1852 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1833 = false ∨ valuation q 1852 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1756)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1853)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 2 11 (meaning1756 q) (meaning1834 q) (meaning1853 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1834 = false ∨ valuation q 1853 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1756)) (literal (valuationOf q) (1835)) (literal (valuationOf q) (1854)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 2 12 (meaning1756 q) (meaning1835 q) (meaning1854 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1835 = false ∨ valuation q 1854 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1849 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1849)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 3 6 (meaning1757 q) (meaning1829 q) (meaning1849 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1829 = false ∨ valuation q 1849 = true := counterClause1542 (baseVal q)

theorem counterClause1543 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1850 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1850)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 3 7 (meaning1757 q) (meaning1830 q) (meaning1850 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1830 = false ∨ valuation q 1850 = true := counterClause1543 (baseVal q)

theorem counterClause1544 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1851 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1851)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 3 8 (meaning1757 q) (meaning1831 q) (meaning1851 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1831 = false ∨ valuation q 1851 = true := counterClause1544 (baseVal q)

theorem counterClause1545 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1852)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 3 9 (meaning1757 q) (meaning1832 q) (meaning1852 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1832 = false ∨ valuation q 1852 = true := counterClause1545 (baseVal q)

theorem counterClause1546 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1853)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 3 10 (meaning1757 q) (meaning1833 q) (meaning1853 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1833 = false ∨ valuation q 1853 = true := counterClause1546 (baseVal q)

theorem counterClause1547 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1849 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1849)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 4 5 (meaning1758 q) (meaning1828 q) (meaning1849 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1828 = false ∨ valuation q 1849 = true := counterClause1547 (baseVal q)

theorem counterClause1548 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1850 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1850)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 4 6 (meaning1758 q) (meaning1829 q) (meaning1850 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1829 = false ∨ valuation q 1850 = true := counterClause1548 (baseVal q)

theorem counterClause1549 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1851 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1851)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 4 7 (meaning1758 q) (meaning1830 q) (meaning1851 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1830 = false ∨ valuation q 1851 = true := counterClause1549 (baseVal q)

theorem counterClause1550 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1852)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 4 8 (meaning1758 q) (meaning1831 q) (meaning1852 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1831 = false ∨ valuation q 1852 = true := counterClause1550 (baseVal q)

theorem counterClause1551 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1853)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 4 9 (meaning1758 q) (meaning1832 q) (meaning1853 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1832 = false ∨ valuation q 1853 = true := counterClause1551 (baseVal q)

theorem counterClause1552 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1854)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 4 10 (meaning1758 q) (meaning1833 q) (meaning1854 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1833 = false ∨ valuation q 1854 = true := counterClause1552 (baseVal q)

theorem counterClause1553 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1849 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1827)) (literal (valuationOf q) (1849)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 5 4 (meaning1759 q) (meaning1827 q) (meaning1849 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1827 = false ∨ valuation q 1849 = true := counterClause1553 (baseVal q)

theorem counterClause1554 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1850 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1850)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 5 5 (meaning1759 q) (meaning1828 q) (meaning1850 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1828 = false ∨ valuation q 1850 = true := counterClause1554 (baseVal q)

theorem counterClause1555 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1851 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1851)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 5 6 (meaning1759 q) (meaning1829 q) (meaning1851 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1829 = false ∨ valuation q 1851 = true := counterClause1555 (baseVal q)

theorem counterClause1556 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1852)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 5 7 (meaning1759 q) (meaning1830 q) (meaning1852 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1830 = false ∨ valuation q 1852 = true := counterClause1556 (baseVal q)

theorem counterClause1557 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1853)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 5 8 (meaning1759 q) (meaning1831 q) (meaning1853 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1831 = false ∨ valuation q 1853 = true := counterClause1557 (baseVal q)

theorem counterClause1558 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1854)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 5 9 (meaning1759 q) (meaning1832 q) (meaning1854 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1832 = false ∨ valuation q 1854 = true := counterClause1558 (baseVal q)

theorem counterClause1559 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1855)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 5 10 (meaning1759 q) (meaning1833 q) (meaning1855 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1833 = false ∨ valuation q 1855 = true := counterClause1559 (baseVal q)

theorem counterClause1560 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1826 = false ∨ valuationOf q 1849 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1826)) (literal (valuationOf q) (1849)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 6 3 (meaning1760 q) (meaning1826 q) (meaning1849 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1826 = false ∨ valuationOf q 1849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1826 = false ∨ valuation q 1849 = true := counterClause1560 (baseVal q)

theorem counterClause1561 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1850 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1827)) (literal (valuationOf q) (1850)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 6 4 (meaning1760 q) (meaning1827 q) (meaning1850 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1827 = false ∨ valuation q 1850 = true := counterClause1561 (baseVal q)

theorem counterClause1562 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1851 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1851)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 6 5 (meaning1760 q) (meaning1828 q) (meaning1851 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1828 = false ∨ valuation q 1851 = true := counterClause1562 (baseVal q)

theorem counterClause1563 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1852)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 6 6 (meaning1760 q) (meaning1829 q) (meaning1852 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1829 = false ∨ valuation q 1852 = true := counterClause1563 (baseVal q)

theorem counterClause1564 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1853)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 6 7 (meaning1760 q) (meaning1830 q) (meaning1853 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1830 = false ∨ valuation q 1853 = true := counterClause1564 (baseVal q)

theorem counterClause1565 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1854)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 6 8 (meaning1760 q) (meaning1831 q) (meaning1854 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1831 = false ∨ valuation q 1854 = true := counterClause1565 (baseVal q)

theorem counterClause1566 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1855)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 6 9 (meaning1760 q) (meaning1832 q) (meaning1855 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1832 = false ∨ valuation q 1855 = true := counterClause1566 (baseVal q)

theorem counterClause1567 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1851 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1827)) (literal (valuationOf q) (1851)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 7 4 (meaning1761 q) (meaning1827 q) (meaning1851 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1827 = false ∨ valuation q 1851 = true := counterClause1567 (baseVal q)

theorem counterClause1568 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1852)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 7 5 (meaning1761 q) (meaning1828 q) (meaning1852 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1828 = false ∨ valuation q 1852 = true := counterClause1568 (baseVal q)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E036.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112036
