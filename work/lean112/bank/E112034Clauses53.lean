import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec53 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1697 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1854)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 8 6 (meaning1761 q) (meaning1829 q) (meaning1854 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1697 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1829 = false ∨ valuation q 1854 = true := counterClause1697 (baseVal q)

theorem counterClause1698 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1855)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 8 7 (meaning1761 q) (meaning1830 q) (meaning1855 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1698 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1830 = false ∨ valuation q 1855 = true := counterClause1698 (baseVal q)

theorem counterClause1699 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1856)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 8 8 (meaning1761 q) (meaning1831 q) (meaning1856 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1699 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1831 = false ∨ valuation q 1856 = true := counterClause1699 (baseVal q)

theorem counterClause1700 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1857 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1857)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 8 9 (meaning1761 q) (meaning1832 q) (meaning1857 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1700 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1832 = false ∨ valuation q 1857 = true := counterClause1700 (baseVal q)

theorem counterClause1701 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1858 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1858)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 8 10 (meaning1761 q) (meaning1833 q) (meaning1858 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1701 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1833 = false ∨ valuation q 1858 = true := counterClause1701 (baseVal q)

theorem counterClause1702 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1854)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 9 5 (meaning1762 q) (meaning1828 q) (meaning1854 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1702 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1828 = false ∨ valuation q 1854 = true := counterClause1702 (baseVal q)

theorem counterClause1703 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1855)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 9 6 (meaning1762 q) (meaning1829 q) (meaning1855 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1703 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1829 = false ∨ valuation q 1855 = true := counterClause1703 (baseVal q)

theorem counterClause1704 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1856)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 9 7 (meaning1762 q) (meaning1830 q) (meaning1856 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1704 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1830 = false ∨ valuation q 1856 = true := counterClause1704 (baseVal q)

theorem counterClause1705 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1857 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1857)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 9 8 (meaning1762 q) (meaning1831 q) (meaning1857 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1705 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1831 = false ∨ valuation q 1857 = true := counterClause1705 (baseVal q)

theorem counterClause1706 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1858 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1858)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 9 9 (meaning1762 q) (meaning1832 q) (meaning1858 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1706 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1832 = false ∨ valuation q 1858 = true := counterClause1706 (baseVal q)

theorem counterClause1707 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1855)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 10 5 (meaning1763 q) (meaning1828 q) (meaning1855 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1707 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1828 = false ∨ valuation q 1855 = true := counterClause1707 (baseVal q)

theorem counterClause1708 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1856)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 10 6 (meaning1763 q) (meaning1829 q) (meaning1856 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1708 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1829 = false ∨ valuation q 1856 = true := counterClause1708 (baseVal q)

theorem counterClause1709 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1858 = false ∨ valuationOf q 1894 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) + (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (l₂ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1858)) (literal (valuationOf q) (1894)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1868 q) 9 18 (meaning1682 q) (meaning1858 q) (meaning1894 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1858 = false ∨ valuationOf q 1894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1709 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1858 = false ∨ valuation q 1894 = true := counterClause1709 (baseVal q)

theorem counterClause1710 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1857 = false ∨ valuationOf q 1894 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) + (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (l₂ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1683)) (literal (valuationOf q) (1857)) (literal (valuationOf q) (1894)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1868 q) 10 17 (meaning1683 q) (meaning1857 q) (meaning1894 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1857 = false ∨ valuationOf q 1894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1710 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1857 = false ∨ valuation q 1894 = true := counterClause1710 (baseVal q)

theorem counterClause1711 (q : Nat → Bool) : valuationOf q 1684 = false ∨ valuationOf q 1856 = false ∨ valuationOf q 1894 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) + (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (l₂ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1684)) (literal (valuationOf q) (1856)) (literal (valuationOf q) (1894)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1868 q) 11 16 (meaning1684 q) (meaning1856 q) (meaning1894 q) hs
  change valuationOf q 1684 = false ∨ valuationOf q 1856 = false ∨ valuationOf q 1894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1711 (q : Snake 81) (h : Conditions q) : valuation q 1684 = false ∨ valuation q 1856 = false ∨ valuation q 1894 = true := counterClause1711 (baseVal q)

theorem counterClause1712 (q : Nat → Bool) : valuationOf q 1685 = false ∨ valuationOf q 1855 = false ∨ valuationOf q 1894 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) + (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (l₂ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1685)) (literal (valuationOf q) (1855)) (literal (valuationOf q) (1894)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1868 q) 12 15 (meaning1685 q) (meaning1855 q) (meaning1894 q) hs
  change valuationOf q 1685 = false ∨ valuationOf q 1855 = false ∨ valuationOf q 1894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1712 (q : Snake 81) (h : Conditions q) : valuation q 1685 = false ∨ valuation q 1855 = false ∨ valuation q 1894 = true := counterClause1712 (baseVal q)

theorem counterClause1713 (q : Nat → Bool) : valuationOf q 1686 = false ∨ valuationOf q 1854 = false ∨ valuationOf q 1894 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) + (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (l₂ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1686)) (literal (valuationOf q) (1854)) (literal (valuationOf q) (1894)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1868 q) 13 14 (meaning1686 q) (meaning1854 q) (meaning1894 q) hs
  change valuationOf q 1686 = false ∨ valuationOf q 1854 = false ∨ valuationOf q 1894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1713 (q : Snake 81) (h : Conditions q) : valuation q 1686 = false ∨ valuation q 1854 = false ∨ valuation q 1894 = true := counterClause1713 (baseVal q)

theorem counterClause1714 (q : Nat → Bool) : valuationOf q 1687 = false ∨ valuationOf q 1853 = false ∨ valuationOf q 1894 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) + (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (l₂ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1687)) (literal (valuationOf q) (1853)) (literal (valuationOf q) (1894)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1868 q) 14 13 (meaning1687 q) (meaning1853 q) (meaning1894 q) hs
  change valuationOf q 1687 = false ∨ valuationOf q 1853 = false ∨ valuationOf q 1894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1714 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1853 = false ∨ valuation q 1894 = true := counterClause1714 (baseVal q)

theorem counterClause1715 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1852 = false ∨ valuationOf q 1894 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) + (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (l₂ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1688)) (literal (valuationOf q) (1852)) (literal (valuationOf q) (1894)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1868 q) 15 12 (meaning1688 q) (meaning1852 q) (meaning1894 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1852 = false ∨ valuationOf q 1894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1715 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1852 = false ∨ valuation q 1894 = true := counterClause1715 (baseVal q)

theorem counterClause1716 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1851 = false ∨ valuationOf q 1894 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) + (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (l₂ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1689)) (literal (valuationOf q) (1851)) (literal (valuationOf q) (1894)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1868 q) 16 11 (meaning1689 q) (meaning1851 q) (meaning1894 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1851 = false ∨ valuationOf q 1894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1716 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1851 = false ∨ valuation q 1894 = true := counterClause1716 (baseVal q)

theorem counterClause1717 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1850 = false ∨ valuationOf q 1894 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) + (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (l₂ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1690)) (literal (valuationOf q) (1850)) (literal (valuationOf q) (1894)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1868 q) 17 10 (meaning1690 q) (meaning1850 q) (meaning1894 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1850 = false ∨ valuationOf q 1894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1717 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1850 = false ∨ valuation q 1894 = true := counterClause1717 (baseVal q)

theorem counterClause1718 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1849 = false ∨ valuationOf q 1894 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) + (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (l₂ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1691)) (literal (valuationOf q) (1849)) (literal (valuationOf q) (1894)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1868 q) 18 9 (meaning1691 q) (meaning1849 q) (meaning1894 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1849 = false ∨ valuationOf q 1894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1718 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1849 = false ∨ valuation q 1894 = true := counterClause1718 (baseVal q)

theorem clause1719 (q : Snake 81) (h : Conditions q) : valuation q 1894 = false := by
  rw [value1894]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1868 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1720 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 22 = false := by
  rw [value14, value16, value19, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (164 : Vertex) (168 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1721 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value14, value16, value86, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (164 : Vertex) (416 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1722 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value16, value17, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (164 : Vertex) (166 : Vertex) (172 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1723 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value17, value18, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (166 : Vertex) (167 : Vertex) (182 : Vertex) (183 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1724 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 36 = false ∨ valuation q 38 = false := by
  rw [value20, value21, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (169 : Vertex) (171 : Vertex) (233 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1725 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 36 = false ∨ valuation q 92 = false ∨ valuation q 114 = false := by
  rw [value20, value36, value92, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (169 : Vertex) (233 : Vertex) (425 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1726 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value27, value28, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (184 : Vertex) (185 : Vertex) (186 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1727 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value32, value33, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (226 : Vertex) (227 : Vertex) (234 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1728 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 107 = false ∨ valuation q 115 = false := by
  rw [value32, value37, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (226 : Vertex) (234 : Vertex) (482 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block53 (q : Snake 81) (h : Conditions q) : B112E034.Block53 (valuation q) :=
  ⟨clause1697 q h, clause1698 q h, clause1699 q h, clause1700 q h, clause1701 q h, clause1702 q h, clause1703 q h, clause1704 q h, clause1705 q h, clause1706 q h, clause1707 q h, clause1708 q h, clause1709 q h, clause1710 q h, clause1711 q h, clause1712 q h, clause1713 q h, clause1714 q h, clause1715 q h, clause1716 q h, clause1717 q h, clause1718 q h, clause1719 q h, clause1720 q h, clause1721 q h, clause1722 q h, clause1723 q h, clause1724 q h, clause1725 q h, clause1726 q h, clause1727 q h, clause1728 q h⟩

end
end Snake9.Regrowth.E112034
