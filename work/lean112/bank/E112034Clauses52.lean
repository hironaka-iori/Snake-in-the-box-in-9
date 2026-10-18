import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec52 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1665 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1849 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1849)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 4 5 (meaning1757 q) (meaning1828 q) (meaning1849 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1665 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1828 = false ∨ valuation q 1849 = true := counterClause1665 (baseVal q)

theorem counterClause1666 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1850 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1850)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 4 6 (meaning1757 q) (meaning1829 q) (meaning1850 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1666 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1829 = false ∨ valuation q 1850 = true := counterClause1666 (baseVal q)

theorem counterClause1667 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1851 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1851)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 4 7 (meaning1757 q) (meaning1830 q) (meaning1851 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1667 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1830 = false ∨ valuation q 1851 = true := counterClause1667 (baseVal q)

theorem counterClause1668 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1852)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 4 8 (meaning1757 q) (meaning1831 q) (meaning1852 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1668 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1831 = false ∨ valuation q 1852 = true := counterClause1668 (baseVal q)

theorem counterClause1669 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1853)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 4 9 (meaning1757 q) (meaning1832 q) (meaning1853 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1669 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1832 = false ∨ valuation q 1853 = true := counterClause1669 (baseVal q)

theorem counterClause1670 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1854)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 4 10 (meaning1757 q) (meaning1833 q) (meaning1854 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1670 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1833 = false ∨ valuation q 1854 = true := counterClause1670 (baseVal q)

theorem counterClause1671 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1855)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 4 11 (meaning1757 q) (meaning1834 q) (meaning1855 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1671 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1834 = false ∨ valuation q 1855 = true := counterClause1671 (baseVal q)

theorem counterClause1672 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1835)) (literal (valuationOf q) (1856)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 4 12 (meaning1757 q) (meaning1835 q) (meaning1856 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1672 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1835 = false ∨ valuation q 1856 = true := counterClause1672 (baseVal q)

theorem counterClause1673 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1850 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1850)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 5 5 (meaning1758 q) (meaning1828 q) (meaning1850 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1673 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1828 = false ∨ valuation q 1850 = true := counterClause1673 (baseVal q)

theorem counterClause1674 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1851 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1851)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 5 6 (meaning1758 q) (meaning1829 q) (meaning1851 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1674 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1829 = false ∨ valuation q 1851 = true := counterClause1674 (baseVal q)

theorem counterClause1675 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1852)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 5 7 (meaning1758 q) (meaning1830 q) (meaning1852 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1675 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1830 = false ∨ valuation q 1852 = true := counterClause1675 (baseVal q)

theorem counterClause1676 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1853)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 5 8 (meaning1758 q) (meaning1831 q) (meaning1853 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1676 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1831 = false ∨ valuation q 1853 = true := counterClause1676 (baseVal q)

theorem counterClause1677 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1854)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 5 9 (meaning1758 q) (meaning1832 q) (meaning1854 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1677 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1832 = false ∨ valuation q 1854 = true := counterClause1677 (baseVal q)

theorem counterClause1678 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1855)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 5 10 (meaning1758 q) (meaning1833 q) (meaning1855 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1678 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1833 = false ∨ valuation q 1855 = true := counterClause1678 (baseVal q)

theorem counterClause1679 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1856)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 5 11 (meaning1758 q) (meaning1834 q) (meaning1856 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1679 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1834 = false ∨ valuation q 1856 = true := counterClause1679 (baseVal q)

theorem counterClause1680 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1857 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1835)) (literal (valuationOf q) (1857)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 5 12 (meaning1758 q) (meaning1835 q) (meaning1857 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1680 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1835 = false ∨ valuation q 1857 = true := counterClause1680 (baseVal q)

theorem counterClause1681 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1851 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1851)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 6 5 (meaning1759 q) (meaning1828 q) (meaning1851 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1681 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1828 = false ∨ valuation q 1851 = true := counterClause1681 (baseVal q)

theorem counterClause1682 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1852)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 6 6 (meaning1759 q) (meaning1829 q) (meaning1852 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1682 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1829 = false ∨ valuation q 1852 = true := counterClause1682 (baseVal q)

theorem counterClause1683 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1853)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 6 7 (meaning1759 q) (meaning1830 q) (meaning1853 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1683 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1830 = false ∨ valuation q 1853 = true := counterClause1683 (baseVal q)

theorem counterClause1684 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1854)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 6 8 (meaning1759 q) (meaning1831 q) (meaning1854 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1684 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1831 = false ∨ valuation q 1854 = true := counterClause1684 (baseVal q)

theorem counterClause1685 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1855)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 6 9 (meaning1759 q) (meaning1832 q) (meaning1855 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1685 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1832 = false ∨ valuation q 1855 = true := counterClause1685 (baseVal q)

theorem counterClause1686 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1856)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 6 10 (meaning1759 q) (meaning1833 q) (meaning1856 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1686 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1833 = false ∨ valuation q 1856 = true := counterClause1686 (baseVal q)

theorem counterClause1687 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1857 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1857)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 6 11 (meaning1759 q) (meaning1834 q) (meaning1857 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1687 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1834 = false ∨ valuation q 1857 = true := counterClause1687 (baseVal q)

theorem counterClause1688 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1858 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1835)) (literal (valuationOf q) (1858)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 6 12 (meaning1759 q) (meaning1835 q) (meaning1858 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1688 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1835 = false ∨ valuation q 1858 = true := counterClause1688 (baseVal q)

theorem counterClause1689 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1851 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1827)) (literal (valuationOf q) (1851)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 7 4 (meaning1760 q) (meaning1827 q) (meaning1851 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1689 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1827 = false ∨ valuation q 1851 = true := counterClause1689 (baseVal q)

theorem counterClause1690 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1852)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 7 5 (meaning1760 q) (meaning1828 q) (meaning1852 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1690 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1828 = false ∨ valuation q 1852 = true := counterClause1690 (baseVal q)

theorem counterClause1691 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1853)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 7 6 (meaning1760 q) (meaning1829 q) (meaning1853 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1691 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1829 = false ∨ valuation q 1853 = true := counterClause1691 (baseVal q)

theorem counterClause1692 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1854)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 7 7 (meaning1760 q) (meaning1830 q) (meaning1854 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1692 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1830 = false ∨ valuation q 1854 = true := counterClause1692 (baseVal q)

theorem counterClause1693 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1855)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 7 8 (meaning1760 q) (meaning1831 q) (meaning1855 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1693 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1831 = false ∨ valuation q 1855 = true := counterClause1693 (baseVal q)

theorem counterClause1694 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1856)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 7 9 (meaning1760 q) (meaning1832 q) (meaning1856 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1694 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1832 = false ∨ valuation q 1856 = true := counterClause1694 (baseVal q)

theorem counterClause1695 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1857 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1857)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 7 10 (meaning1760 q) (meaning1833 q) (meaning1857 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1695 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1833 = false ∨ valuation q 1857 = true := counterClause1695 (baseVal q)

theorem counterClause1696 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1853)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 8 5 (meaning1761 q) (meaning1828 q) (meaning1853 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1696 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1828 = false ∨ valuation q 1853 = true := counterClause1696 (baseVal q)

theorem block52 (q : Snake 81) (h : Conditions q) : B112E034.Block52 (valuation q) :=
  ⟨clause1665 q h, clause1666 q h, clause1667 q h, clause1668 q h, clause1669 q h, clause1670 q h, clause1671 q h, clause1672 q h, clause1673 q h, clause1674 q h, clause1675 q h, clause1676 q h, clause1677 q h, clause1678 q h, clause1679 q h, clause1680 q h, clause1681 q h, clause1682 q h, clause1683 q h, clause1684 q h, clause1685 q h, clause1686 q h, clause1687 q h, clause1688 q h, clause1689 q h, clause1690 q h, clause1691 q h, clause1692 q h, clause1693 q h, clause1694 q h, clause1695 q h, clause1696 q h⟩

end
end Snake9.Regrowth.E112034
