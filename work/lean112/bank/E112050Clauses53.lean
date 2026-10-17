import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec53 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1697 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1853)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 6 7 (meaning1760 q) (meaning1830 q) (meaning1853 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1697 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1830 = false ∨ valuation q 1853 = true := counterClause1697 (baseVal q)

theorem counterClause1698 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1854)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 6 8 (meaning1760 q) (meaning1831 q) (meaning1854 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1698 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1831 = false ∨ valuation q 1854 = true := counterClause1698 (baseVal q)

theorem counterClause1699 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1855)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 6 9 (meaning1760 q) (meaning1832 q) (meaning1855 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1699 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1832 = false ∨ valuation q 1855 = true := counterClause1699 (baseVal q)

theorem counterClause1700 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1856)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 6 10 (meaning1760 q) (meaning1833 q) (meaning1856 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1700 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1833 = false ∨ valuation q 1856 = true := counterClause1700 (baseVal q)

theorem counterClause1701 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1857 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1857)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 6 11 (meaning1760 q) (meaning1834 q) (meaning1857 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1701 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1834 = false ∨ valuation q 1857 = true := counterClause1701 (baseVal q)

theorem counterClause1702 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1851 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1827)) (literal (valuationOf q) (1851)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 7 4 (meaning1761 q) (meaning1827 q) (meaning1851 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1702 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1827 = false ∨ valuation q 1851 = true := counterClause1702 (baseVal q)

theorem counterClause1703 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1852)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 7 5 (meaning1761 q) (meaning1828 q) (meaning1852 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1703 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1828 = false ∨ valuation q 1852 = true := counterClause1703 (baseVal q)

theorem counterClause1704 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1853)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 7 6 (meaning1761 q) (meaning1829 q) (meaning1853 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1704 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1829 = false ∨ valuation q 1853 = true := counterClause1704 (baseVal q)

theorem counterClause1705 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1854)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 7 7 (meaning1761 q) (meaning1830 q) (meaning1854 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1705 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1830 = false ∨ valuation q 1854 = true := counterClause1705 (baseVal q)

theorem counterClause1706 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1855)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 7 8 (meaning1761 q) (meaning1831 q) (meaning1855 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1706 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1831 = false ∨ valuation q 1855 = true := counterClause1706 (baseVal q)

theorem counterClause1707 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1856)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 7 9 (meaning1761 q) (meaning1832 q) (meaning1856 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1707 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1832 = false ∨ valuation q 1856 = true := counterClause1707 (baseVal q)

theorem counterClause1708 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1857 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1857)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 7 10 (meaning1761 q) (meaning1833 q) (meaning1857 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1708 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1833 = false ∨ valuation q 1857 = true := counterClause1708 (baseVal q)

theorem counterClause1709 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1827)) (literal (valuationOf q) (1852)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 8 4 (meaning1762 q) (meaning1827 q) (meaning1852 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1709 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1827 = false ∨ valuation q 1852 = true := counterClause1709 (baseVal q)

theorem counterClause1710 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1853)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 8 5 (meaning1762 q) (meaning1828 q) (meaning1853 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1710 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1828 = false ∨ valuation q 1853 = true := counterClause1710 (baseVal q)

theorem counterClause1711 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1854)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 8 6 (meaning1762 q) (meaning1829 q) (meaning1854 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1711 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1829 = false ∨ valuation q 1854 = true := counterClause1711 (baseVal q)

theorem counterClause1712 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1855)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 8 7 (meaning1762 q) (meaning1830 q) (meaning1855 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1712 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1830 = false ∨ valuation q 1855 = true := counterClause1712 (baseVal q)

theorem counterClause1713 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1856)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 8 8 (meaning1762 q) (meaning1831 q) (meaning1856 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1713 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1831 = false ∨ valuation q 1856 = true := counterClause1713 (baseVal q)

theorem counterClause1714 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1857 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1857)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 8 9 (meaning1762 q) (meaning1832 q) (meaning1857 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1714 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1832 = false ∨ valuation q 1857 = true := counterClause1714 (baseVal q)

theorem counterClause1715 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1858 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1858)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 8 10 (meaning1762 q) (meaning1833 q) (meaning1858 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1715 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1833 = false ∨ valuation q 1858 = true := counterClause1715 (baseVal q)

theorem counterClause1716 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1859 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1859)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 8 11 (meaning1762 q) (meaning1834 q) (meaning1859 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1716 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1834 = false ∨ valuation q 1859 = true := counterClause1716 (baseVal q)

theorem counterClause1717 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1827)) (literal (valuationOf q) (1853)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 9 4 (meaning1763 q) (meaning1827 q) (meaning1853 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1717 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1827 = false ∨ valuation q 1853 = true := counterClause1717 (baseVal q)

theorem counterClause1718 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1854)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 9 5 (meaning1763 q) (meaning1828 q) (meaning1854 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1718 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1828 = false ∨ valuation q 1854 = true := counterClause1718 (baseVal q)

theorem counterClause1719 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1855)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 9 6 (meaning1763 q) (meaning1829 q) (meaning1855 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1719 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1829 = false ∨ valuation q 1855 = true := counterClause1719 (baseVal q)

theorem counterClause1720 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1856)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 9 7 (meaning1763 q) (meaning1830 q) (meaning1856 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1720 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1830 = false ∨ valuation q 1856 = true := counterClause1720 (baseVal q)

theorem counterClause1721 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1857 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1857)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 9 8 (meaning1763 q) (meaning1831 q) (meaning1857 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1721 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1831 = false ∨ valuation q 1857 = true := counterClause1721 (baseVal q)

theorem counterClause1722 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1858 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1858)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 9 9 (meaning1763 q) (meaning1832 q) (meaning1858 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1722 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1832 = false ∨ valuation q 1858 = true := counterClause1722 (baseVal q)

theorem counterClause1723 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1859 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1859)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 9 10 (meaning1763 q) (meaning1833 q) (meaning1859 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1723 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1833 = false ∨ valuation q 1859 = true := counterClause1723 (baseVal q)

theorem counterClause1724 (q : Nat → Bool) : valuationOf q 1764 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1764)) (literal (valuationOf q) (1827)) (literal (valuationOf q) (1854)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 10 4 (meaning1764 q) (meaning1827 q) (meaning1854 q) hs
  change valuationOf q 1764 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1724 (q : Snake 81) (h : Conditions q) : valuation q 1764 = false ∨ valuation q 1827 = false ∨ valuation q 1854 = true := counterClause1724 (baseVal q)

theorem counterClause1725 (q : Nat → Bool) : valuationOf q 1764 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1764)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1855)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 10 5 (meaning1764 q) (meaning1828 q) (meaning1855 q) hs
  change valuationOf q 1764 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1725 (q : Snake 81) (h : Conditions q) : valuation q 1764 = false ∨ valuation q 1828 = false ∨ valuation q 1855 = true := counterClause1725 (baseVal q)

theorem counterClause1726 (q : Nat → Bool) : valuationOf q 1764 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1764)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1856)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 10 6 (meaning1764 q) (meaning1829 q) (meaning1856 q) hs
  change valuationOf q 1764 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1726 (q : Snake 81) (h : Conditions q) : valuation q 1764 = false ∨ valuation q 1829 = false ∨ valuation q 1856 = true := counterClause1726 (baseVal q)

theorem counterClause1727 (q : Nat → Bool) : valuationOf q 1764 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1857 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1764)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1857)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 10 7 (meaning1764 q) (meaning1830 q) (meaning1857 q) hs
  change valuationOf q 1764 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1727 (q : Snake 81) (h : Conditions q) : valuation q 1764 = false ∨ valuation q 1830 = false ∨ valuation q 1857 = true := counterClause1727 (baseVal q)

theorem counterClause1728 (q : Nat → Bool) : valuationOf q 1764 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1858 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1764)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1858)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 10 8 (meaning1764 q) (meaning1831 q) (meaning1858 q) hs
  change valuationOf q 1764 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1728 (q : Snake 81) (h : Conditions q) : valuation q 1764 = false ∨ valuation q 1831 = false ∨ valuation q 1858 = true := counterClause1728 (baseVal q)

theorem block53 (q : Snake 81) (h : Conditions q) : B112E050.Block53 (valuation q) :=
  ⟨clause1697 q h, clause1698 q h, clause1699 q h, clause1700 q h, clause1701 q h, clause1702 q h, clause1703 q h, clause1704 q h, clause1705 q h, clause1706 q h, clause1707 q h, clause1708 q h, clause1709 q h, clause1710 q h, clause1711 q h, clause1712 q h, clause1713 q h, clause1714 q h, clause1715 q h, clause1716 q h, clause1717 q h, clause1718 q h, clause1719 q h, clause1720 q h, clause1721 q h, clause1722 q h, clause1723 q h, clause1724 q h, clause1725 q h, clause1726 q h, clause1727 q h, clause1728 q h⟩

end
end Snake9.Regrowth.E112050
