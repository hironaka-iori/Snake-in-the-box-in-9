import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec57 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1825 (q : Nat → Bool) : valuationOf q 1802 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1836 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1802)) (literal (valuationOf q) (1822)) (literal (valuationOf q) (1836)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 6 2 (meaning1802 q) (meaning1822 q) (meaning1836 q) hs
  change valuationOf q 1802 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1825 (q : Snake 81) (h : Conditions q) : valuation q 1802 = false ∨ valuation q 1822 = false ∨ valuation q 1836 = true := counterClause1825 (baseVal q)

theorem counterClause1826 (q : Nat → Bool) : valuationOf q 1767 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1853 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1767)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1853)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 3 6 (meaning1767 q) (meaning1834 q) (meaning1853 q) hs
  change valuationOf q 1767 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1826 (q : Snake 81) (h : Conditions q) : valuation q 1767 = false ∨ valuation q 1834 = false ∨ valuation q 1853 = true := counterClause1826 (baseVal q)

theorem counterClause1827 (q : Nat → Bool) : valuationOf q 1768 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1853 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1768)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1853)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 4 5 (meaning1768 q) (meaning1833 q) (meaning1853 q) hs
  change valuationOf q 1768 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1827 (q : Snake 81) (h : Conditions q) : valuation q 1768 = false ∨ valuation q 1833 = false ∨ valuation q 1853 = true := counterClause1827 (baseVal q)

theorem counterClause1828 (q : Nat → Bool) : valuationOf q 1768 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1854 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1768)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1854)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 4 6 (meaning1768 q) (meaning1834 q) (meaning1854 q) hs
  change valuationOf q 1768 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1828 (q : Snake 81) (h : Conditions q) : valuation q 1768 = false ∨ valuation q 1834 = false ∨ valuation q 1854 = true := counterClause1828 (baseVal q)

theorem counterClause1829 (q : Nat → Bool) : valuationOf q 1768 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1855 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1768)) (literal (valuationOf q) (1835)) (literal (valuationOf q) (1855)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 4 7 (meaning1768 q) (meaning1835 q) (meaning1855 q) hs
  change valuationOf q 1768 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1829 (q : Snake 81) (h : Conditions q) : valuation q 1768 = false ∨ valuation q 1835 = false ∨ valuation q 1855 = true := counterClause1829 (baseVal q)

theorem counterClause1830 (q : Nat → Bool) : valuationOf q 1768 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1856 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1768)) (literal (valuationOf q) (1836)) (literal (valuationOf q) (1856)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 4 8 (meaning1768 q) (meaning1836 q) (meaning1856 q) hs
  change valuationOf q 1768 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1830 (q : Snake 81) (h : Conditions q) : valuation q 1768 = false ∨ valuation q 1836 = false ∨ valuation q 1856 = true := counterClause1830 (baseVal q)

theorem counterClause1831 (q : Nat → Bool) : valuationOf q 1768 = false ∨ valuationOf q 1837 = false ∨ valuationOf q 1857 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1768)) (literal (valuationOf q) (1837)) (literal (valuationOf q) (1857)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 4 9 (meaning1768 q) (meaning1837 q) (meaning1857 q) hs
  change valuationOf q 1768 = false ∨ valuationOf q 1837 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1831 (q : Snake 81) (h : Conditions q) : valuation q 1768 = false ∨ valuation q 1837 = false ∨ valuation q 1857 = true := counterClause1831 (baseVal q)

theorem counterClause1832 (q : Nat → Bool) : valuationOf q 1769 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1853 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1769)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1853)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 5 4 (meaning1769 q) (meaning1832 q) (meaning1853 q) hs
  change valuationOf q 1769 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1832 (q : Snake 81) (h : Conditions q) : valuation q 1769 = false ∨ valuation q 1832 = false ∨ valuation q 1853 = true := counterClause1832 (baseVal q)

theorem counterClause1833 (q : Nat → Bool) : valuationOf q 1769 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1854 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1769)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1854)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 5 5 (meaning1769 q) (meaning1833 q) (meaning1854 q) hs
  change valuationOf q 1769 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1833 (q : Snake 81) (h : Conditions q) : valuation q 1769 = false ∨ valuation q 1833 = false ∨ valuation q 1854 = true := counterClause1833 (baseVal q)

theorem counterClause1834 (q : Nat → Bool) : valuationOf q 1769 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1855 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1769)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1855)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 5 6 (meaning1769 q) (meaning1834 q) (meaning1855 q) hs
  change valuationOf q 1769 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1834 (q : Snake 81) (h : Conditions q) : valuation q 1769 = false ∨ valuation q 1834 = false ∨ valuation q 1855 = true := counterClause1834 (baseVal q)

theorem counterClause1835 (q : Nat → Bool) : valuationOf q 1769 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1856 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1769)) (literal (valuationOf q) (1835)) (literal (valuationOf q) (1856)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 5 7 (meaning1769 q) (meaning1835 q) (meaning1856 q) hs
  change valuationOf q 1769 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1835 (q : Snake 81) (h : Conditions q) : valuation q 1769 = false ∨ valuation q 1835 = false ∨ valuation q 1856 = true := counterClause1835 (baseVal q)

theorem counterClause1836 (q : Nat → Bool) : valuationOf q 1769 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1857 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1769)) (literal (valuationOf q) (1836)) (literal (valuationOf q) (1857)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 5 8 (meaning1769 q) (meaning1836 q) (meaning1857 q) hs
  change valuationOf q 1769 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1836 (q : Snake 81) (h : Conditions q) : valuation q 1769 = false ∨ valuation q 1836 = false ∨ valuation q 1857 = true := counterClause1836 (baseVal q)

theorem counterClause1837 (q : Nat → Bool) : valuationOf q 1769 = false ∨ valuationOf q 1837 = false ∨ valuationOf q 1858 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1769)) (literal (valuationOf q) (1837)) (literal (valuationOf q) (1858)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 5 9 (meaning1769 q) (meaning1837 q) (meaning1858 q) hs
  change valuationOf q 1769 = false ∨ valuationOf q 1837 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1837 (q : Snake 81) (h : Conditions q) : valuation q 1769 = false ∨ valuation q 1837 = false ∨ valuation q 1858 = true := counterClause1837 (baseVal q)

theorem counterClause1838 (q : Nat → Bool) : valuationOf q 1769 = false ∨ valuationOf q 1838 = false ∨ valuationOf q 1859 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1769)) (literal (valuationOf q) (1838)) (literal (valuationOf q) (1859)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 5 10 (meaning1769 q) (meaning1838 q) (meaning1859 q) hs
  change valuationOf q 1769 = false ∨ valuationOf q 1838 = false ∨ valuationOf q 1859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1838 (q : Snake 81) (h : Conditions q) : valuation q 1769 = false ∨ valuation q 1838 = false ∨ valuation q 1859 = true := counterClause1838 (baseVal q)

theorem counterClause1839 (q : Nat → Bool) : valuationOf q 1770 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1853 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1770)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1853)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 6 3 (meaning1770 q) (meaning1831 q) (meaning1853 q) hs
  change valuationOf q 1770 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1839 (q : Snake 81) (h : Conditions q) : valuation q 1770 = false ∨ valuation q 1831 = false ∨ valuation q 1853 = true := counterClause1839 (baseVal q)

theorem counterClause1840 (q : Nat → Bool) : valuationOf q 1770 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1854 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1770)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1854)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 6 4 (meaning1770 q) (meaning1832 q) (meaning1854 q) hs
  change valuationOf q 1770 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1840 (q : Snake 81) (h : Conditions q) : valuation q 1770 = false ∨ valuation q 1832 = false ∨ valuation q 1854 = true := counterClause1840 (baseVal q)

theorem counterClause1841 (q : Nat → Bool) : valuationOf q 1770 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1855 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1770)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1855)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 6 5 (meaning1770 q) (meaning1833 q) (meaning1855 q) hs
  change valuationOf q 1770 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1841 (q : Snake 81) (h : Conditions q) : valuation q 1770 = false ∨ valuation q 1833 = false ∨ valuation q 1855 = true := counterClause1841 (baseVal q)

theorem counterClause1842 (q : Nat → Bool) : valuationOf q 1770 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1856 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1770)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1856)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 6 6 (meaning1770 q) (meaning1834 q) (meaning1856 q) hs
  change valuationOf q 1770 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1842 (q : Snake 81) (h : Conditions q) : valuation q 1770 = false ∨ valuation q 1834 = false ∨ valuation q 1856 = true := counterClause1842 (baseVal q)

theorem counterClause1843 (q : Nat → Bool) : valuationOf q 1770 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1857 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1770)) (literal (valuationOf q) (1835)) (literal (valuationOf q) (1857)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 6 7 (meaning1770 q) (meaning1835 q) (meaning1857 q) hs
  change valuationOf q 1770 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1843 (q : Snake 81) (h : Conditions q) : valuation q 1770 = false ∨ valuation q 1835 = false ∨ valuation q 1857 = true := counterClause1843 (baseVal q)

theorem counterClause1844 (q : Nat → Bool) : valuationOf q 1770 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1858 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1770)) (literal (valuationOf q) (1836)) (literal (valuationOf q) (1858)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 6 8 (meaning1770 q) (meaning1836 q) (meaning1858 q) hs
  change valuationOf q 1770 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1844 (q : Snake 81) (h : Conditions q) : valuation q 1770 = false ∨ valuation q 1836 = false ∨ valuation q 1858 = true := counterClause1844 (baseVal q)

theorem counterClause1845 (q : Nat → Bool) : valuationOf q 1770 = false ∨ valuationOf q 1837 = false ∨ valuationOf q 1859 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1770)) (literal (valuationOf q) (1837)) (literal (valuationOf q) (1859)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 6 9 (meaning1770 q) (meaning1837 q) (meaning1859 q) hs
  change valuationOf q 1770 = false ∨ valuationOf q 1837 = false ∨ valuationOf q 1859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1845 (q : Snake 81) (h : Conditions q) : valuation q 1770 = false ∨ valuation q 1837 = false ∨ valuation q 1859 = true := counterClause1845 (baseVal q)

theorem counterClause1846 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1854 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1854)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 7 3 (meaning1771 q) (meaning1831 q) (meaning1854 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1846 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1831 = false ∨ valuation q 1854 = true := counterClause1846 (baseVal q)

theorem counterClause1847 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1855 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1855)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 7 4 (meaning1771 q) (meaning1832 q) (meaning1855 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1847 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1832 = false ∨ valuation q 1855 = true := counterClause1847 (baseVal q)

theorem counterClause1848 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1856 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1856)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 7 5 (meaning1771 q) (meaning1833 q) (meaning1856 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1848 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1833 = false ∨ valuation q 1856 = true := counterClause1848 (baseVal q)

theorem counterClause1849 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1857 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1857)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 7 6 (meaning1771 q) (meaning1834 q) (meaning1857 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1849 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1834 = false ∨ valuation q 1857 = true := counterClause1849 (baseVal q)

theorem counterClause1850 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1858 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1835)) (literal (valuationOf q) (1858)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 7 7 (meaning1771 q) (meaning1835 q) (meaning1858 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1850 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1835 = false ∨ valuation q 1858 = true := counterClause1850 (baseVal q)

theorem counterClause1851 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1859 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1836)) (literal (valuationOf q) (1859)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 7 8 (meaning1771 q) (meaning1836 q) (meaning1859 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1851 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1836 = false ∨ valuation q 1859 = true := counterClause1851 (baseVal q)

theorem counterClause1852 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1854 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1854)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 8 2 (meaning1772 q) (meaning1830 q) (meaning1854 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1852 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1830 = false ∨ valuation q 1854 = true := counterClause1852 (baseVal q)

theorem counterClause1853 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1855 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1855)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 8 3 (meaning1772 q) (meaning1831 q) (meaning1855 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1853 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1831 = false ∨ valuation q 1855 = true := counterClause1853 (baseVal q)

theorem counterClause1854 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1856 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1856)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 8 4 (meaning1772 q) (meaning1832 q) (meaning1856 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1854 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1832 = false ∨ valuation q 1856 = true := counterClause1854 (baseVal q)

theorem counterClause1855 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1857 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1857)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 8 5 (meaning1772 q) (meaning1833 q) (meaning1857 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1855 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1833 = false ∨ valuation q 1857 = true := counterClause1855 (baseVal q)

theorem counterClause1856 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1858 = true := by
  have hs : count1845 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1858)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]) (count1845 q) 8 6 (meaning1772 q) (meaning1834 q) (meaning1858 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1856 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1834 = false ∨ valuation q 1858 = true := counterClause1856 (baseVal q)

theorem block57 (q : Snake 81) (h : Conditions q) : B112E055.Block57 (valuation q) :=
  ⟨clause1825 q h, clause1826 q h, clause1827 q h, clause1828 q h, clause1829 q h, clause1830 q h, clause1831 q h, clause1832 q h, clause1833 q h, clause1834 q h, clause1835 q h, clause1836 q h, clause1837 q h, clause1838 q h, clause1839 q h, clause1840 q h, clause1841 q h, clause1842 q h, clause1843 q h, clause1844 q h, clause1845 q h, clause1846 q h, clause1847 q h, clause1848 q h, clause1849 q h, clause1850 q h, clause1851 q h, clause1852 q h, clause1853 q h, clause1854 q h, clause1855 q h, clause1856 q h⟩

end
end Snake9.Regrowth.E112055
