import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec53 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1697 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1734 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1734)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 3 7 (meaning1653 q) (meaning1716 q) (meaning1734 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1697 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1716 = false ∨ valuation q 1734 = true := counterClause1697 (baseVal q)

theorem counterClause1698 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1735 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1735)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 3 8 (meaning1653 q) (meaning1717 q) (meaning1735 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1698 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1717 = false ∨ valuation q 1735 = true := counterClause1698 (baseVal q)

theorem counterClause1699 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1736 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1736)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 3 9 (meaning1653 q) (meaning1718 q) (meaning1736 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1699 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1718 = false ∨ valuation q 1736 = true := counterClause1699 (baseVal q)

theorem counterClause1700 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1737 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1737)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 3 10 (meaning1653 q) (meaning1719 q) (meaning1737 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1700 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1719 = false ∨ valuation q 1737 = true := counterClause1700 (baseVal q)

theorem counterClause1701 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1738 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1738)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 3 11 (meaning1653 q) (meaning1720 q) (meaning1738 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1701 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1720 = false ∨ valuation q 1738 = true := counterClause1701 (baseVal q)

theorem counterClause1702 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1732 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1732)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 4 4 (meaning1654 q) (meaning1713 q) (meaning1732 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1702 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1713 = false ∨ valuation q 1732 = true := counterClause1702 (baseVal q)

theorem counterClause1703 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1733 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1733)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 4 5 (meaning1654 q) (meaning1714 q) (meaning1733 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1703 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1714 = false ∨ valuation q 1733 = true := counterClause1703 (baseVal q)

theorem counterClause1704 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1734 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1734)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 4 6 (meaning1654 q) (meaning1715 q) (meaning1734 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1704 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1715 = false ∨ valuation q 1734 = true := counterClause1704 (baseVal q)

theorem counterClause1705 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1735 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1735)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 4 7 (meaning1654 q) (meaning1716 q) (meaning1735 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1705 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1716 = false ∨ valuation q 1735 = true := counterClause1705 (baseVal q)

theorem counterClause1706 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1736 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1736)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 4 8 (meaning1654 q) (meaning1717 q) (meaning1736 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1706 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1717 = false ∨ valuation q 1736 = true := counterClause1706 (baseVal q)

theorem counterClause1707 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1737 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1737)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 4 9 (meaning1654 q) (meaning1718 q) (meaning1737 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1707 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1718 = false ∨ valuation q 1737 = true := counterClause1707 (baseVal q)

theorem counterClause1708 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1738 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1738)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 4 10 (meaning1654 q) (meaning1719 q) (meaning1738 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1708 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1719 = false ∨ valuation q 1738 = true := counterClause1708 (baseVal q)

theorem counterClause1709 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1739 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1739)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 4 11 (meaning1654 q) (meaning1720 q) (meaning1739 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1709 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1720 = false ∨ valuation q 1739 = true := counterClause1709 (baseVal q)

theorem counterClause1710 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1732 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1712)) (literal (valuationOf q) (1732)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 5 3 (meaning1655 q) (meaning1712 q) (meaning1732 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1710 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1712 = false ∨ valuation q 1732 = true := counterClause1710 (baseVal q)

theorem counterClause1711 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1733 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1733)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 5 4 (meaning1655 q) (meaning1713 q) (meaning1733 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1711 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1713 = false ∨ valuation q 1733 = true := counterClause1711 (baseVal q)

theorem counterClause1712 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1734 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1734)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 5 5 (meaning1655 q) (meaning1714 q) (meaning1734 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1712 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1714 = false ∨ valuation q 1734 = true := counterClause1712 (baseVal q)

theorem counterClause1713 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1735 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1735)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 5 6 (meaning1655 q) (meaning1715 q) (meaning1735 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1713 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1715 = false ∨ valuation q 1735 = true := counterClause1713 (baseVal q)

theorem counterClause1714 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1736 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1736)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 5 7 (meaning1655 q) (meaning1716 q) (meaning1736 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1714 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1716 = false ∨ valuation q 1736 = true := counterClause1714 (baseVal q)

theorem counterClause1715 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1737 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1737)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 5 8 (meaning1655 q) (meaning1717 q) (meaning1737 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1715 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1717 = false ∨ valuation q 1737 = true := counterClause1715 (baseVal q)

theorem counterClause1716 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1738 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1738)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 5 9 (meaning1655 q) (meaning1718 q) (meaning1738 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1716 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1718 = false ∨ valuation q 1738 = true := counterClause1716 (baseVal q)

theorem counterClause1717 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1739 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1739)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 5 10 (meaning1655 q) (meaning1719 q) (meaning1739 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1717 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1719 = false ∨ valuation q 1739 = true := counterClause1717 (baseVal q)

theorem counterClause1718 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1733 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1712)) (literal (valuationOf q) (1733)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 6 3 (meaning1656 q) (meaning1712 q) (meaning1733 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1718 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1712 = false ∨ valuation q 1733 = true := counterClause1718 (baseVal q)

theorem counterClause1719 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1734 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1734)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 6 4 (meaning1656 q) (meaning1713 q) (meaning1734 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1719 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1713 = false ∨ valuation q 1734 = true := counterClause1719 (baseVal q)

theorem counterClause1720 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1735 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1735)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 6 5 (meaning1656 q) (meaning1714 q) (meaning1735 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1720 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1714 = false ∨ valuation q 1735 = true := counterClause1720 (baseVal q)

theorem counterClause1721 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1736 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1736)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 6 6 (meaning1656 q) (meaning1715 q) (meaning1736 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1721 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1715 = false ∨ valuation q 1736 = true := counterClause1721 (baseVal q)

theorem counterClause1722 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1737 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1737)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 6 7 (meaning1656 q) (meaning1716 q) (meaning1737 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1722 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1716 = false ∨ valuation q 1737 = true := counterClause1722 (baseVal q)

theorem counterClause1723 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1738 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1738)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 6 8 (meaning1656 q) (meaning1717 q) (meaning1738 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1723 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1717 = false ∨ valuation q 1738 = true := counterClause1723 (baseVal q)

theorem counterClause1724 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1739 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1739)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 6 9 (meaning1656 q) (meaning1718 q) (meaning1739 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1724 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1718 = false ∨ valuation q 1739 = true := counterClause1724 (baseVal q)

theorem counterClause1725 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1734 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1712)) (literal (valuationOf q) (1734)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 7 3 (meaning1657 q) (meaning1712 q) (meaning1734 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1725 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1712 = false ∨ valuation q 1734 = true := counterClause1725 (baseVal q)

theorem counterClause1726 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1735 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1735)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 7 4 (meaning1657 q) (meaning1713 q) (meaning1735 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1726 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1713 = false ∨ valuation q 1735 = true := counterClause1726 (baseVal q)

theorem counterClause1727 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1736 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1736)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 7 5 (meaning1657 q) (meaning1714 q) (meaning1736 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1727 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1714 = false ∨ valuation q 1736 = true := counterClause1727 (baseVal q)

theorem counterClause1728 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1737 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1737)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 7 6 (meaning1657 q) (meaning1715 q) (meaning1737 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1728 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1715 = false ∨ valuation q 1737 = true := counterClause1728 (baseVal q)

theorem block53 (q : Snake 81) (h : Conditions q) : B112E019.Block53 (valuation q) :=
  ⟨clause1697 q h, clause1698 q h, clause1699 q h, clause1700 q h, clause1701 q h, clause1702 q h, clause1703 q h, clause1704 q h, clause1705 q h, clause1706 q h, clause1707 q h, clause1708 q h, clause1709 q h, clause1710 q h, clause1711 q h, clause1712 q h, clause1713 q h, clause1714 q h, clause1715 q h, clause1716 q h, clause1717 q h, clause1718 q h, clause1719 q h, clause1720 q h, clause1721 q h, clause1722 q h, clause1723 q h, clause1724 q h, clause1725 q h, clause1726 q h, clause1727 q h, clause1728 q h⟩

end
end Snake9.Regrowth.E112019
