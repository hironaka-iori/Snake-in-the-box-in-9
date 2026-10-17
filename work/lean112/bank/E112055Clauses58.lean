import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec58 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1857 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1859 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1835)) (literal (valuationOf q) (1859)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 8 7 (meaning1772 q) (meaning1835 q) (meaning1859 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1857 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1835 = false ∨ valuation q 1859 = true := counterClause1857 (baseVal q)

theorem counterClause1858 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1860 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1836)) (literal (valuationOf q) (1860)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 8 8 (meaning1772 q) (meaning1836 q) (meaning1860 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1858 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1836 = false ∨ valuation q 1860 = true := counterClause1858 (baseVal q)

theorem counterClause1859 (q : Nat → Bool) : valuationOf q 1773 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1855 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1773)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1855)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 9 2 (meaning1773 q) (meaning1830 q) (meaning1855 q) hs
  change valuationOf q 1773 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1859 (q : Snake 81) (h : Conditions q) : valuation q 1773 = false ∨ valuation q 1830 = false ∨ valuation q 1855 = true := counterClause1859 (baseVal q)

theorem counterClause1860 (q : Nat → Bool) : valuationOf q 1773 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1856 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1773)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1856)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 9 3 (meaning1773 q) (meaning1831 q) (meaning1856 q) hs
  change valuationOf q 1773 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1860 (q : Snake 81) (h : Conditions q) : valuation q 1773 = false ∨ valuation q 1831 = false ∨ valuation q 1856 = true := counterClause1860 (baseVal q)

theorem counterClause1861 (q : Nat → Bool) : valuationOf q 1773 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1857 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1773)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1857)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 9 4 (meaning1773 q) (meaning1832 q) (meaning1857 q) hs
  change valuationOf q 1773 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1861 (q : Snake 81) (h : Conditions q) : valuation q 1773 = false ∨ valuation q 1832 = false ∨ valuation q 1857 = true := counterClause1861 (baseVal q)

theorem counterClause1862 (q : Nat → Bool) : valuationOf q 1773 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1858 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1773)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1858)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 9 5 (meaning1773 q) (meaning1833 q) (meaning1858 q) hs
  change valuationOf q 1773 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1862 (q : Snake 81) (h : Conditions q) : valuation q 1773 = false ∨ valuation q 1833 = false ∨ valuation q 1858 = true := counterClause1862 (baseVal q)

theorem counterClause1863 (q : Nat → Bool) : valuationOf q 1773 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1859 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1773)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1859)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 9 6 (meaning1773 q) (meaning1834 q) (meaning1859 q) hs
  change valuationOf q 1773 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1863 (q : Snake 81) (h : Conditions q) : valuation q 1773 = false ∨ valuation q 1834 = false ∨ valuation q 1859 = true := counterClause1863 (baseVal q)

theorem counterClause1864 (q : Nat → Bool) : valuationOf q 1773 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1860 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1773)) (literal (valuationOf q) (1835)) (literal (valuationOf q) (1860)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 9 7 (meaning1773 q) (meaning1835 q) (meaning1860 q) hs
  change valuationOf q 1773 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1864 (q : Snake 81) (h : Conditions q) : valuation q 1773 = false ∨ valuation q 1835 = false ∨ valuation q 1860 = true := counterClause1864 (baseVal q)

theorem counterClause1865 (q : Nat → Bool) : valuationOf q 1774 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1856 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1774)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1856)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 10 2 (meaning1774 q) (meaning1830 q) (meaning1856 q) hs
  change valuationOf q 1774 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1865 (q : Snake 81) (h : Conditions q) : valuation q 1774 = false ∨ valuation q 1830 = false ∨ valuation q 1856 = true := counterClause1865 (baseVal q)

theorem counterClause1866 (q : Nat → Bool) : valuationOf q 1774 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1857 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1774)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1857)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 10 3 (meaning1774 q) (meaning1831 q) (meaning1857 q) hs
  change valuationOf q 1774 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1866 (q : Snake 81) (h : Conditions q) : valuation q 1774 = false ∨ valuation q 1831 = false ∨ valuation q 1857 = true := counterClause1866 (baseVal q)

theorem counterClause1867 (q : Nat → Bool) : valuationOf q 1774 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1858 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1774)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1858)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 10 4 (meaning1774 q) (meaning1832 q) (meaning1858 q) hs
  change valuationOf q 1774 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1867 (q : Snake 81) (h : Conditions q) : valuation q 1774 = false ∨ valuation q 1832 = false ∨ valuation q 1858 = true := counterClause1867 (baseVal q)

theorem counterClause1868 (q : Nat → Bool) : valuationOf q 1774 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1859 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1774)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1859)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 10 5 (meaning1774 q) (meaning1833 q) (meaning1859 q) hs
  change valuationOf q 1774 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1868 (q : Snake 81) (h : Conditions q) : valuation q 1774 = false ∨ valuation q 1833 = false ∨ valuation q 1859 = true := counterClause1868 (baseVal q)

theorem counterClause1869 (q : Nat → Bool) : valuationOf q 1774 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1860 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1774)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1860)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 10 6 (meaning1774 q) (meaning1834 q) (meaning1860 q) hs
  change valuationOf q 1774 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1869 (q : Snake 81) (h : Conditions q) : valuation q 1774 = false ∨ valuation q 1834 = false ∨ valuation q 1860 = true := counterClause1869 (baseVal q)

theorem counterClause1870 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1857 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1857)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 11 2 (meaning1775 q) (meaning1830 q) (meaning1857 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1870 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1830 = false ∨ valuation q 1857 = true := counterClause1870 (baseVal q)

theorem counterClause1871 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1858 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1858)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 11 3 (meaning1775 q) (meaning1831 q) (meaning1858 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1871 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1831 = false ∨ valuation q 1858 = true := counterClause1871 (baseVal q)

theorem counterClause1872 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1859 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1859)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 11 4 (meaning1775 q) (meaning1832 q) (meaning1859 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1872 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1832 = false ∨ valuation q 1859 = true := counterClause1872 (baseVal q)

theorem counterClause1873 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1860 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1860)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 11 5 (meaning1775 q) (meaning1833 q) (meaning1860 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1873 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1833 = false ∨ valuation q 1860 = true := counterClause1873 (baseVal q)

theorem counterClause1874 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1858 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1858)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 12 2 (meaning1776 q) (meaning1830 q) (meaning1858 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1874 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1830 = false ∨ valuation q 1858 = true := counterClause1874 (baseVal q)

theorem counterClause1875 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1859 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1859)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 12 3 (meaning1776 q) (meaning1831 q) (meaning1859 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1875 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1831 = false ∨ valuation q 1859 = true := counterClause1875 (baseVal q)

theorem counterClause1876 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1860 = false ∨ valuationOf q 1890 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) + (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (l₂ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1860)) (literal (valuationOf q) (1890)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1868 q) 7 16 (meaning1700 q) (meaning1860 q) (meaning1890 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1860 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1876 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1860 = false ∨ valuation q 1890 = true := counterClause1876 (baseVal q)

theorem counterClause1877 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1859 = false ∨ valuationOf q 1890 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) + (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (l₂ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1859)) (literal (valuationOf q) (1890)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1868 q) 8 15 (meaning1701 q) (meaning1859 q) (meaning1890 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1859 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1877 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1859 = false ∨ valuation q 1890 = true := counterClause1877 (baseVal q)

theorem counterClause1878 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1858 = false ∨ valuationOf q 1890 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) + (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (l₂ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1858)) (literal (valuationOf q) (1890)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1868 q) 9 14 (meaning1702 q) (meaning1858 q) (meaning1890 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1858 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1878 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1858 = false ∨ valuation q 1890 = true := counterClause1878 (baseVal q)

theorem counterClause1879 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1857 = false ∨ valuationOf q 1890 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) + (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (l₂ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1857)) (literal (valuationOf q) (1890)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1868 q) 10 13 (meaning1703 q) (meaning1857 q) (meaning1890 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1857 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1879 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1857 = false ∨ valuation q 1890 = true := counterClause1879 (baseVal q)

theorem counterClause1880 (q : Nat → Bool) : valuationOf q 1704 = false ∨ valuationOf q 1856 = false ∨ valuationOf q 1890 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) + (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (l₂ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1704)) (literal (valuationOf q) (1856)) (literal (valuationOf q) (1890)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1868 q) 11 12 (meaning1704 q) (meaning1856 q) (meaning1890 q) hs
  change valuationOf q 1704 = false ∨ valuationOf q 1856 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1880 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1856 = false ∨ valuation q 1890 = true := counterClause1880 (baseVal q)

theorem counterClause1881 (q : Nat → Bool) : valuationOf q 1705 = false ∨ valuationOf q 1855 = false ∨ valuationOf q 1890 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) + (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (l₂ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1705)) (literal (valuationOf q) (1855)) (literal (valuationOf q) (1890)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1868 q) 12 11 (meaning1705 q) (meaning1855 q) (meaning1890 q) hs
  change valuationOf q 1705 = false ∨ valuationOf q 1855 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1881 (q : Snake 81) (h : Conditions q) : valuation q 1705 = false ∨ valuation q 1855 = false ∨ valuation q 1890 = true := counterClause1881 (baseVal q)

theorem counterClause1882 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1854 = false ∨ valuationOf q 1890 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) + (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (l₂ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1706)) (literal (valuationOf q) (1854)) (literal (valuationOf q) (1890)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1868 q) 13 10 (meaning1706 q) (meaning1854 q) (meaning1890 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1854 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1882 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1854 = false ∨ valuation q 1890 = true := counterClause1882 (baseVal q)

theorem counterClause1883 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1853 = false ∨ valuationOf q 1890 = true := by
  have hs : count1868 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) + (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (l₂ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1853)) (literal (valuationOf q) (1890)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1868 q) 14 9 (meaning1707 q) (meaning1853 q) (meaning1890 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1853 = false ∨ valuationOf q 1890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1883 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1853 = false ∨ valuation q 1890 = true := counterClause1883 (baseVal q)

theorem clause1884 (q : Snake 81) (h : Conditions q) : valuation q 1890 = false := by
  rw [value1890]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1868 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1885 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 6 = false := by
  rw [value1, value3, value5, value6]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (2 : Vertex) (8 : Vertex) (10 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1886 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 4 = false ∨ valuation q 10 = false ∨ valuation q 13 = false := by
  rw [value2, value4, value10, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (1 : Vertex) (5 : Vertex) (17 : Vertex) (21 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1887 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 13 = false ∨ valuation q 71 = false ∨ valuation q 83 = false := by
  rw [value4, value13, value71, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (5 : Vertex) (21 : Vertex) (261 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1888 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 40 = false ∨ valuation q 71 = false ∨ valuation q 112 = false := by
  rw [value4, value40, value71, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (5 : Vertex) (133 : Vertex) (261 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block58 (q : Snake 81) (h : Conditions q) : B112E055.Block58 (valuation q) :=
  ⟨clause1857 q h, clause1858 q h, clause1859 q h, clause1860 q h, clause1861 q h, clause1862 q h, clause1863 q h, clause1864 q h, clause1865 q h, clause1866 q h, clause1867 q h, clause1868 q h, clause1869 q h, clause1870 q h, clause1871 q h, clause1872 q h, clause1873 q h, clause1874 q h, clause1875 q h, clause1876 q h, clause1877 q h, clause1878 q h, clause1879 q h, clause1880 q h, clause1881 q h, clause1882 q h, clause1883 q h, clause1884 q h, clause1885 q h, clause1886 q h, clause1887 q h, clause1888 q h⟩

end
end Snake9.Regrowth.E112055
