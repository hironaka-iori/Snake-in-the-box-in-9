import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1689 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_left (literal (valuationOf q) (1657)) (literal (valuationOf q) (1689)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 3 (meaning1657 q) (meaning1689 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1689 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1690 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1690)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 3 1 (meaning1657 q) (meaning1679 q) (meaning1690 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1679 = false ∨ valuation q 1690 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1691 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1691)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 3 2 (meaning1657 q) (meaning1680 q) (meaning1691 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1680 = false ∨ valuation q 1691 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1692 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1692)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 3 3 (meaning1657 q) (meaning1681 q) (meaning1692 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1681 = false ∨ valuation q 1692 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1693 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1693)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 3 4 (meaning1657 q) (meaning1682 q) (meaning1693 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1682 = false ∨ valuation q 1693 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1694 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1694)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 3 5 (meaning1657 q) (meaning1683 q) (meaning1694 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1683 = false ∨ valuation q 1694 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1690 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_left (literal (valuationOf q) (1658)) (literal (valuationOf q) (1690)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 4 (meaning1658 q) (meaning1690 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1690 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1691 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1691)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 4 1 (meaning1658 q) (meaning1679 q) (meaning1691 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1679 = false ∨ valuation q 1691 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1692 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1692)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 4 2 (meaning1658 q) (meaning1680 q) (meaning1692 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1680 = false ∨ valuation q 1692 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1693 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1693)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 4 3 (meaning1658 q) (meaning1681 q) (meaning1693 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1681 = false ∨ valuation q 1693 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1694 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1694)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 4 4 (meaning1658 q) (meaning1682 q) (meaning1694 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1682 = false ∨ valuation q 1694 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1692 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1692)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 5 1 (meaning1659 q) (meaning1679 q) (meaning1692 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1679 = false ∨ valuation q 1692 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1693 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1693)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 5 2 (meaning1659 q) (meaning1680 q) (meaning1693 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1680 = false ∨ valuation q 1693 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1694 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1694)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 5 3 (meaning1659 q) (meaning1681 q) (meaning1694 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1681 = false ∨ valuation q 1694 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1695 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1695)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 5 4 (meaning1659 q) (meaning1682 q) (meaning1695 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1682 = false ∨ valuation q 1695 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1692 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_left (literal (valuationOf q) (1660)) (literal (valuationOf q) (1692)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 6 (meaning1660 q) (meaning1692 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1692 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1693 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1693)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 6 1 (meaning1660 q) (meaning1679 q) (meaning1693 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1679 = false ∨ valuation q 1693 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1694 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1694)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 6 2 (meaning1660 q) (meaning1680 q) (meaning1694 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1680 = false ∨ valuation q 1694 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1695 = true := by
  have hs : count1687 q = (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) + (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95, -98, -99, -105, -106]) (l₂ := [-109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1695)) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106]) (countLit q [-109, -110, -111, -113, -115, -116, -117, -120]) (count1687 q) 6 3 (meaning1660 q) (meaning1681 q) (meaning1695 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1681 = false ∨ valuation q 1695 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1708 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1708)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 2 4 (meaning1625 q) (meaning1690 q) (meaning1708 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1690 = false ∨ valuation q 1708 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1712 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1712)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 2 8 (meaning1625 q) (meaning1694 q) (meaning1712 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1694 = false ∨ valuation q 1712 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1713 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1713)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 2 9 (meaning1625 q) (meaning1695 q) (meaning1713 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1695 = false ∨ valuation q 1713 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1706 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1706)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 3 1 (meaning1626 q) (meaning1687 q) (meaning1706 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1687 = false ∨ valuation q 1706 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1707 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1707)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 3 2 (meaning1626 q) (meaning1688 q) (meaning1707 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1688 = false ∨ valuation q 1707 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1708 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1708)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 3 3 (meaning1626 q) (meaning1689 q) (meaning1708 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1689 = false ∨ valuation q 1708 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1709 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1709)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 3 4 (meaning1626 q) (meaning1690 q) (meaning1709 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1690 = false ∨ valuation q 1709 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1710 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1710)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 3 5 (meaning1626 q) (meaning1691 q) (meaning1710 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1691 = false ∨ valuation q 1710 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1711 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1711)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 3 6 (meaning1626 q) (meaning1692 q) (meaning1711 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1692 = false ∨ valuation q 1711 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1712 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1712)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 3 7 (meaning1626 q) (meaning1693 q) (meaning1712 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1693 = false ∨ valuation q 1712 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1713 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1713)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 3 8 (meaning1626 q) (meaning1694 q) (meaning1713 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1694 = false ∨ valuation q 1713 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1707 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1707)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 4 1 (meaning1627 q) (meaning1687 q) (meaning1707 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1687 = false ∨ valuation q 1707 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1708 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) + (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (l₂ := [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1708)) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]) (countLit q [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1703 q) 4 2 (meaning1627 q) (meaning1688 q) (meaning1708 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1688 = false ∨ valuation q 1708 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E040.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112040
