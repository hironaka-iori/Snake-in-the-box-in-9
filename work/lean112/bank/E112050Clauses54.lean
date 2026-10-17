import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec54 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1729 (q : Nat → Bool) : valuationOf q 1764 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1859 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1764)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1859)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 10 9 (meaning1764 q) (meaning1832 q) (meaning1859 q) hs
  change valuationOf q 1764 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1729 (q : Snake 81) (h : Conditions q) : valuation q 1764 = false ∨ valuation q 1832 = false ∨ valuation q 1859 = true := counterClause1729 (baseVal q)

theorem counterClause1730 (q : Nat → Bool) : valuationOf q 1765 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1765)) (literal (valuationOf q) (1827)) (literal (valuationOf q) (1855)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 11 4 (meaning1765 q) (meaning1827 q) (meaning1855 q) hs
  change valuationOf q 1765 = false ∨ valuationOf q 1827 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1730 (q : Snake 81) (h : Conditions q) : valuation q 1765 = false ∨ valuation q 1827 = false ∨ valuation q 1855 = true := counterClause1730 (baseVal q)

theorem counterClause1731 (q : Nat → Bool) : valuationOf q 1765 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1765)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1856)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 11 5 (meaning1765 q) (meaning1828 q) (meaning1856 q) hs
  change valuationOf q 1765 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1731 (q : Snake 81) (h : Conditions q) : valuation q 1765 = false ∨ valuation q 1828 = false ∨ valuation q 1856 = true := counterClause1731 (baseVal q)

theorem counterClause1732 (q : Nat → Bool) : valuationOf q 1765 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1857 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1765)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1857)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 11 6 (meaning1765 q) (meaning1829 q) (meaning1857 q) hs
  change valuationOf q 1765 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1732 (q : Snake 81) (h : Conditions q) : valuation q 1765 = false ∨ valuation q 1829 = false ∨ valuation q 1857 = true := counterClause1732 (baseVal q)

theorem counterClause1733 (q : Nat → Bool) : valuationOf q 1765 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1858 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1765)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1858)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 11 7 (meaning1765 q) (meaning1830 q) (meaning1858 q) hs
  change valuationOf q 1765 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1733 (q : Snake 81) (h : Conditions q) : valuation q 1765 = false ∨ valuation q 1830 = false ∨ valuation q 1858 = true := counterClause1733 (baseVal q)

theorem counterClause1734 (q : Nat → Bool) : valuationOf q 1765 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1859 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1765)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1859)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 11 8 (meaning1765 q) (meaning1831 q) (meaning1859 q) hs
  change valuationOf q 1765 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1734 (q : Snake 81) (h : Conditions q) : valuation q 1765 = false ∨ valuation q 1831 = false ∨ valuation q 1859 = true := counterClause1734 (baseVal q)

theorem counterClause1735 (q : Nat → Bool) : valuationOf q 1765 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1860 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1765)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1860)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 11 9 (meaning1765 q) (meaning1832 q) (meaning1860 q) hs
  change valuationOf q 1765 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1735 (q : Snake 81) (h : Conditions q) : valuation q 1765 = false ∨ valuation q 1832 = false ∨ valuation q 1860 = true := counterClause1735 (baseVal q)

theorem counterClause1736 (q : Nat → Bool) : valuationOf q 1766 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1857 = true := by
  have hs : count1841 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) + (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (l₂ := [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1766)) (literal (valuationOf q) (1828)) (literal (valuationOf q) (1857)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95]) (countLit q [-96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1841 q) 12 5 (meaning1766 q) (meaning1828 q) (meaning1857 q) hs
  change valuationOf q 1766 = false ∨ valuationOf q 1828 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1736 (q : Snake 81) (h : Conditions q) : valuation q 1766 = false ∨ valuation q 1828 = false ∨ valuation q 1857 = true := counterClause1736 (baseVal q)

theorem counterClause1737 (q : Nat → Bool) : valuationOf q 1686 = false ∨ valuationOf q 1860 = false ∨ valuationOf q 1890 = true := by
  have hs : count1866 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1686)) (literal (valuationOf q) (1860)) (literal (valuationOf q) (1890)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1866 q) 5 20 (meaning1686 q) (meaning1860 q) (meaning1890 q) hs
  change valuationOf q 1686 = false ∨ valuationOf q 1860 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1737 (q : Snake 81) (h : Conditions q) : valuation q 1686 = false ∨ valuation q 1860 = false ∨ valuation q 1890 = true := counterClause1737 (baseVal q)

theorem counterClause1738 (q : Nat → Bool) : valuationOf q 1687 = false ∨ valuationOf q 1859 = false ∨ valuationOf q 1890 = true := by
  have hs : count1866 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1687)) (literal (valuationOf q) (1859)) (literal (valuationOf q) (1890)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1866 q) 6 19 (meaning1687 q) (meaning1859 q) (meaning1890 q) hs
  change valuationOf q 1687 = false ∨ valuationOf q 1859 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1738 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1859 = false ∨ valuation q 1890 = true := counterClause1738 (baseVal q)

theorem counterClause1739 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1858 = false ∨ valuationOf q 1890 = true := by
  have hs : count1866 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1688)) (literal (valuationOf q) (1858)) (literal (valuationOf q) (1890)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1866 q) 7 18 (meaning1688 q) (meaning1858 q) (meaning1890 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1858 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1739 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1858 = false ∨ valuation q 1890 = true := counterClause1739 (baseVal q)

theorem counterClause1740 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1857 = false ∨ valuationOf q 1890 = true := by
  have hs : count1866 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1689)) (literal (valuationOf q) (1857)) (literal (valuationOf q) (1890)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1866 q) 8 17 (meaning1689 q) (meaning1857 q) (meaning1890 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1857 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1740 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1857 = false ∨ valuation q 1890 = true := counterClause1740 (baseVal q)

theorem counterClause1741 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1856 = false ∨ valuationOf q 1890 = true := by
  have hs : count1866 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1690)) (literal (valuationOf q) (1856)) (literal (valuationOf q) (1890)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1866 q) 9 16 (meaning1690 q) (meaning1856 q) (meaning1890 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1856 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1741 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1856 = false ∨ valuation q 1890 = true := counterClause1741 (baseVal q)

theorem counterClause1742 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1855 = false ∨ valuationOf q 1890 = true := by
  have hs : count1866 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1691)) (literal (valuationOf q) (1855)) (literal (valuationOf q) (1890)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1866 q) 10 15 (meaning1691 q) (meaning1855 q) (meaning1890 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1855 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1742 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1855 = false ∨ valuation q 1890 = true := counterClause1742 (baseVal q)

theorem counterClause1743 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1854 = false ∨ valuationOf q 1890 = true := by
  have hs : count1866 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1692)) (literal (valuationOf q) (1854)) (literal (valuationOf q) (1890)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1866 q) 11 14 (meaning1692 q) (meaning1854 q) (meaning1890 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1854 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1743 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1854 = false ∨ valuation q 1890 = true := counterClause1743 (baseVal q)

theorem counterClause1744 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1853 = false ∨ valuationOf q 1890 = true := by
  have hs : count1866 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1853)) (literal (valuationOf q) (1890)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1866 q) 12 13 (meaning1693 q) (meaning1853 q) (meaning1890 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1853 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1744 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1853 = false ∨ valuation q 1890 = true := counterClause1744 (baseVal q)

theorem counterClause1745 (q : Nat → Bool) : valuationOf q 1694 = false ∨ valuationOf q 1852 = false ∨ valuationOf q 1890 = true := by
  have hs : count1866 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1694)) (literal (valuationOf q) (1852)) (literal (valuationOf q) (1890)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1866 q) 13 12 (meaning1694 q) (meaning1852 q) (meaning1890 q) hs
  change valuationOf q 1694 = false ∨ valuationOf q 1852 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1745 (q : Snake 81) (h : Conditions q) : valuation q 1694 = false ∨ valuation q 1852 = false ∨ valuation q 1890 = true := counterClause1745 (baseVal q)

theorem counterClause1746 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1851 = false ∨ valuationOf q 1890 = true := by
  have hs : count1866 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1695)) (literal (valuationOf q) (1851)) (literal (valuationOf q) (1890)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1866 q) 14 11 (meaning1695 q) (meaning1851 q) (meaning1890 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1851 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1746 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1851 = false ∨ valuation q 1890 = true := counterClause1746 (baseVal q)

theorem counterClause1747 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1850 = false ∨ valuationOf q 1890 = true := by
  have hs : count1866 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1850)) (literal (valuationOf q) (1890)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79, -82, -83, -85, -87, -88, -91, -92, -95, -96, -97, -100, -101, -103, -104, -108, -109, -111, -113, -115, -119, -121, -123, -124, -127, -128]) (count1866 q) 15 10 (meaning1696 q) (meaning1850 q) (meaning1890 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1850 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1747 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1850 = false ∨ valuation q 1890 = true := counterClause1747 (baseVal q)

theorem clause1748 (q : Snake 81) (h : Conditions q) : valuation q 1890 = false := by
  rw [value1890]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1866 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1749 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value15, value16, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (131 : Vertex) (146 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1750 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 22 = false := by
  rw [value17, value18, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (133 : Vertex) (140 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1751 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value17, value18, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (133 : Vertex) (388 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1752 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 22 = false ∨ valuation q 89 = false ∨ valuation q 96 = false := by
  rw [value18, value22, value89, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (133 : Vertex) (141 : Vertex) (389 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1753 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 93 = false ∨ valuation q 95 = false := by
  rw [value19, value20, value93, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (137 : Vertex) (139 : Vertex) (393 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1754 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 93 = false ∨ valuation q 96 = false := by
  rw [value19, value22, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (137 : Vertex) (141 : Vertex) (393 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1755 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 31 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value27, value31, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (151 : Vertex) (159 : Vertex) (407 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1756 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 44 = false ∨ valuation q 102 = false ∨ valuation q 123 = false := by
  rw [value27, value44, value102, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (151 : Vertex) (215 : Vertex) (407 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1757 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value32, value33, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (194 : Vertex) (200 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1758 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value34, value35, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (198 : Vertex) (199 : Vertex) (214 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1759 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 44 = false ∨ valuation q 114 = false ∨ valuation q 123 = false := by
  rw [value35, value44, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (199 : Vertex) (215 : Vertex) (455 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1760 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value36, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (200 : Vertex) (202 : Vertex) (204 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block54 (q : Snake 81) (h : Conditions q) : B112E050.Block54 (valuation q) :=
  ⟨clause1729 q h, clause1730 q h, clause1731 q h, clause1732 q h, clause1733 q h, clause1734 q h, clause1735 q h, clause1736 q h, clause1737 q h, clause1738 q h, clause1739 q h, clause1740 q h, clause1741 q h, clause1742 q h, clause1743 q h, clause1744 q h, clause1745 q h, clause1746 q h, clause1747 q h, clause1748 q h, clause1749 q h, clause1750 q h, clause1751 q h, clause1752 q h, clause1753 q h, clause1754 q h, clause1755 q h, clause1756 q h, clause1757 q h, clause1758 q h, clause1759 q h, clause1760 q h⟩

end
end Snake9.Regrowth.E112050
