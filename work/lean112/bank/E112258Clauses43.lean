import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1735 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1735)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 4 2 (meaning1702 q) (meaning1723 q) (meaning1735 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1723 = false ∨ valuation q 1735 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1736 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1736)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 4 3 (meaning1702 q) (meaning1724 q) (meaning1736 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1724 = false ∨ valuation q 1736 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1737 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1737)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 4 4 (meaning1702 q) (meaning1725 q) (meaning1737 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1725 = false ∨ valuation q 1737 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1738 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1738)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 4 5 (meaning1702 q) (meaning1726 q) (meaning1738 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1726 = false ∨ valuation q 1738 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1735 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1735)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 5 1 (meaning1703 q) (meaning1722 q) (meaning1735 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1722 = false ∨ valuation q 1735 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1736 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1736)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 5 2 (meaning1703 q) (meaning1723 q) (meaning1736 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1723 = false ∨ valuation q 1736 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1737 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1737)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 5 3 (meaning1703 q) (meaning1724 q) (meaning1737 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1724 = false ∨ valuation q 1737 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1738 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1738)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 5 4 (meaning1703 q) (meaning1725 q) (meaning1738 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1725 = false ∨ valuation q 1738 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 1704 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1737 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1704)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1737)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 6 2 (meaning1704 q) (meaning1723 q) (meaning1737 q) hs
  change valuationOf q 1704 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1723 = false ∨ valuation q 1737 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 1704 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1739 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1704)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1739)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 6 4 (meaning1704 q) (meaning1725 q) (meaning1739 q) hs
  change valuationOf q 1704 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1725 = false ∨ valuation q 1739 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1751 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_right (literal (valuationOf q) (1736)) (literal (valuationOf q) (1751)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 7 (meaning1736 q) (meaning1751 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1751 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1750 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1750)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 1 5 (meaning1672 q) (meaning1734 q) (meaning1750 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1734 = false ∨ valuation q 1750 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1751 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1751)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 1 6 (meaning1672 q) (meaning1735 q) (meaning1751 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1735 = false ∨ valuation q 1751 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1752)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 1 7 (meaning1672 q) (meaning1736 q) (meaning1752 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1736 = false ∨ valuation q 1752 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1753)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 1 8 (meaning1672 q) (meaning1737 q) (meaning1753 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1737 = false ∨ valuation q 1753 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1738)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 1 9 (meaning1672 q) (meaning1738 q) (meaning1754 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1738 = false ∨ valuation q 1754 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1739)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 1 10 (meaning1672 q) (meaning1739 q) (meaning1755 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1739 = false ∨ valuation q 1755 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1749 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1749)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 2 3 (meaning1673 q) (meaning1732 q) (meaning1749 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1732 = false ∨ valuation q 1749 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1750 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1750)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 2 4 (meaning1673 q) (meaning1733 q) (meaning1750 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1733 = false ∨ valuation q 1750 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1751 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1751)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 2 5 (meaning1673 q) (meaning1734 q) (meaning1751 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1734 = false ∨ valuation q 1751 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1752)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 2 6 (meaning1673 q) (meaning1735 q) (meaning1752 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1735 = false ∨ valuation q 1752 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1753)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 2 7 (meaning1673 q) (meaning1736 q) (meaning1753 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1736 = false ∨ valuation q 1753 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 2 8 (meaning1673 q) (meaning1737 q) (meaning1754 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1737 = false ∨ valuation q 1754 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1738)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 2 9 (meaning1673 q) (meaning1738 q) (meaning1755 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1738 = false ∨ valuation q 1755 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1750 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1750)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 3 3 (meaning1674 q) (meaning1732 q) (meaning1750 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1732 = false ∨ valuation q 1750 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1751 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1751)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 3 4 (meaning1674 q) (meaning1733 q) (meaning1751 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1733 = false ∨ valuation q 1751 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1752)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 3 5 (meaning1674 q) (meaning1734 q) (meaning1752 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1734 = false ∨ valuation q 1752 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1753)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 3 6 (meaning1674 q) (meaning1735 q) (meaning1753 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1735 = false ∨ valuation q 1753 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 3 7 (meaning1674 q) (meaning1736 q) (meaning1754 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1736 = false ∨ valuation q 1754 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 3 8 (meaning1674 q) (meaning1737 q) (meaning1755 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1737 = false ∨ valuation q 1755 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1750 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1750)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 4 2 (meaning1675 q) (meaning1731 q) (meaning1750 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1731 = false ∨ valuation q 1750 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1751 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) + (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (l₂ := [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1751)) (countLit q [-65, -66, -67, -69, -73, -77, -78, -79, -81, -82, -84, -85, -86, -88]) (countLit q [-90, -93, -94, -98, -99, -102, -105, -107, -108, -111, -112, -113, -116, -119, -120]) (count1745 q) 4 3 (meaning1675 q) (meaning1732 q) (meaning1751 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1732 = false ∨ valuation q 1751 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E258.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112258
