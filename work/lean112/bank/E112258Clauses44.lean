import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1752)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 4 4 (meaning1675 q) (meaning1733 q) (meaning1752 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1733 = false ∨ valuation q 1752 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1753)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 4 5 (meaning1675 q) (meaning1734 q) (meaning1753 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1734 = false ∨ valuation q 1753 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 4 6 (meaning1675 q) (meaning1735 q) (meaning1754 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1735 = false ∨ valuation q 1754 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 4 7 (meaning1675 q) (meaning1736 q) (meaning1755 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1736 = false ∨ valuation q 1755 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1756 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1756)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 4 8 (meaning1675 q) (meaning1737 q) (meaning1756 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1737 = false ∨ valuation q 1756 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1751 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1751)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 5 2 (meaning1676 q) (meaning1731 q) (meaning1751 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1731 = false ∨ valuation q 1751 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1752)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 5 3 (meaning1676 q) (meaning1732 q) (meaning1752 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1732 = false ∨ valuation q 1752 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1753)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 5 4 (meaning1676 q) (meaning1733 q) (meaning1753 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1733 = false ∨ valuation q 1753 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 5 5 (meaning1676 q) (meaning1734 q) (meaning1754 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1734 = false ∨ valuation q 1754 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 5 6 (meaning1676 q) (meaning1735 q) (meaning1755 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1735 = false ∨ valuation q 1755 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1756 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1756)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 5 7 (meaning1676 q) (meaning1736 q) (meaning1756 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1736 = false ∨ valuation q 1756 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1757 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1757)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 5 8 (meaning1676 q) (meaning1737 q) (meaning1757 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1737 = false ∨ valuation q 1757 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1752)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 6 2 (meaning1677 q) (meaning1731 q) (meaning1752 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1731 = false ∨ valuation q 1752 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1753)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 6 3 (meaning1677 q) (meaning1732 q) (meaning1753 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1732 = false ∨ valuation q 1753 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 6 4 (meaning1677 q) (meaning1733 q) (meaning1754 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1733 = false ∨ valuation q 1754 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 6 5 (meaning1677 q) (meaning1734 q) (meaning1755 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1734 = false ∨ valuation q 1755 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1756 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1756)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 6 6 (meaning1677 q) (meaning1735 q) (meaning1756 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1735 = false ∨ valuation q 1756 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1757 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1757)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 6 7 (meaning1677 q) (meaning1736 q) (meaning1757 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1736 = false ∨ valuation q 1757 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 7 3 (meaning1678 q) (meaning1732 q) (meaning1754 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1732 = false ∨ valuation q 1754 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 7 4 (meaning1678 q) (meaning1733 q) (meaning1755 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1733 = false ∨ valuation q 1755 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1756 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1756)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 7 5 (meaning1678 q) (meaning1734 q) (meaning1756 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1734 = false ∨ valuation q 1756 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1757 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1757)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 7 6 (meaning1678 q) (meaning1735 q) (meaning1757 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1735 = false ∨ valuation q 1757 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1758 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1758)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 7 7 (meaning1678 q) (meaning1736 q) (meaning1758 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1736 = false ∨ valuation q 1758 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1759 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1759)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 7 8 (meaning1678 q) (meaning1737 q) (meaning1759 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1737 = false ∨ valuation q 1759 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 8 2 (meaning1679 q) (meaning1731 q) (meaning1754 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1731 = false ∨ valuation q 1754 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 8 3 (meaning1679 q) (meaning1732 q) (meaning1755 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1732 = false ∨ valuation q 1755 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1756 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1756)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 8 4 (meaning1679 q) (meaning1733 q) (meaning1756 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1733 = false ∨ valuation q 1756 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1757 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1757)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 8 5 (meaning1679 q) (meaning1734 q) (meaning1757 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1734 = false ∨ valuation q 1757 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1758 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1758)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 8 6 (meaning1679 q) (meaning1735 q) (meaning1758 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1735 = false ∨ valuation q 1758 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 9 2 (meaning1680 q) (meaning1731 q) (meaning1755 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1731 = false ∨ valuation q 1755 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1756 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1756)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 9 3 (meaning1680 q) (meaning1732 q) (meaning1756 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1732 = false ∨ valuation q 1756 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1758 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1758)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 9 5 (meaning1680 q) (meaning1734 q) (meaning1758 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1734 = false ∨ valuation q 1758 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E258.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112258
