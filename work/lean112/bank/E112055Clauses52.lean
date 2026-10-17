import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec52 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1665 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1770 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1770)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 3 3 (meaning1735 q) (meaning1759 q) (meaning1770 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1665 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1759 = false ∨ valuation q 1770 = true := counterClause1665 (baseVal q)

theorem counterClause1666 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1771 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1771)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 3 4 (meaning1735 q) (meaning1760 q) (meaning1771 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1666 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1760 = false ∨ valuation q 1771 = true := counterClause1666 (baseVal q)

theorem counterClause1667 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1772 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1772)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 3 5 (meaning1735 q) (meaning1761 q) (meaning1772 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1667 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1761 = false ∨ valuation q 1772 = true := counterClause1667 (baseVal q)

theorem counterClause1668 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1773 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1773)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 3 6 (meaning1735 q) (meaning1762 q) (meaning1773 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1668 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1762 = false ∨ valuation q 1773 = true := counterClause1668 (baseVal q)

theorem counterClause1669 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1774 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1774)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 3 7 (meaning1735 q) (meaning1763 q) (meaning1774 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1669 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1763 = false ∨ valuation q 1774 = true := counterClause1669 (baseVal q)

theorem counterClause1670 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1768 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_left (literal (valuationOf q) (1736)) (literal (valuationOf q) (1768)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 4 (meaning1736 q) (meaning1768 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1670 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1768 = true := counterClause1670 (baseVal q)

theorem counterClause1671 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1769 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1769)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 4 1 (meaning1736 q) (meaning1757 q) (meaning1769 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1671 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1757 = false ∨ valuation q 1769 = true := counterClause1671 (baseVal q)

theorem counterClause1672 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1770 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1770)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 4 2 (meaning1736 q) (meaning1758 q) (meaning1770 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1672 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1758 = false ∨ valuation q 1770 = true := counterClause1672 (baseVal q)

theorem counterClause1673 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1771 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1771)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 4 3 (meaning1736 q) (meaning1759 q) (meaning1771 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1673 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1759 = false ∨ valuation q 1771 = true := counterClause1673 (baseVal q)

theorem counterClause1674 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1772 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1772)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 4 4 (meaning1736 q) (meaning1760 q) (meaning1772 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1674 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1760 = false ∨ valuation q 1772 = true := counterClause1674 (baseVal q)

theorem counterClause1675 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1773 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1773)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 4 5 (meaning1736 q) (meaning1761 q) (meaning1773 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1675 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1761 = false ∨ valuation q 1773 = true := counterClause1675 (baseVal q)

theorem counterClause1676 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1774 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1774)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 4 6 (meaning1736 q) (meaning1762 q) (meaning1774 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1676 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1762 = false ∨ valuation q 1774 = true := counterClause1676 (baseVal q)

theorem counterClause1677 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1775 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1775)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 4 7 (meaning1736 q) (meaning1763 q) (meaning1775 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1677 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1763 = false ∨ valuation q 1775 = true := counterClause1677 (baseVal q)

theorem counterClause1678 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1769 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_left (literal (valuationOf q) (1737)) (literal (valuationOf q) (1769)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 5 (meaning1737 q) (meaning1769 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1678 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1769 = true := counterClause1678 (baseVal q)

theorem counterClause1679 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1770 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1770)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 5 1 (meaning1737 q) (meaning1757 q) (meaning1770 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1679 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1757 = false ∨ valuation q 1770 = true := counterClause1679 (baseVal q)

theorem counterClause1680 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1771 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1771)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 5 2 (meaning1737 q) (meaning1758 q) (meaning1771 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1680 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1758 = false ∨ valuation q 1771 = true := counterClause1680 (baseVal q)

theorem counterClause1681 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1772 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1772)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 5 3 (meaning1737 q) (meaning1759 q) (meaning1772 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1681 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1759 = false ∨ valuation q 1772 = true := counterClause1681 (baseVal q)

theorem counterClause1682 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1773 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1773)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 5 4 (meaning1737 q) (meaning1760 q) (meaning1773 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1682 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1760 = false ∨ valuation q 1773 = true := counterClause1682 (baseVal q)

theorem counterClause1683 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1774 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1774)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 5 5 (meaning1737 q) (meaning1761 q) (meaning1774 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1683 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1761 = false ∨ valuation q 1774 = true := counterClause1683 (baseVal q)

theorem counterClause1684 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1775 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1775)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 5 6 (meaning1737 q) (meaning1762 q) (meaning1775 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1684 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1762 = false ∨ valuation q 1775 = true := counterClause1684 (baseVal q)

theorem counterClause1685 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1776 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1776)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 5 7 (meaning1737 q) (meaning1763 q) (meaning1776 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1685 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1763 = false ∨ valuation q 1776 = true := counterClause1685 (baseVal q)

theorem counterClause1686 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1770 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_left (literal (valuationOf q) (1738)) (literal (valuationOf q) (1770)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 6 (meaning1738 q) (meaning1770 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1686 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1770 = true := counterClause1686 (baseVal q)

theorem counterClause1687 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1771 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1771)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 6 1 (meaning1738 q) (meaning1757 q) (meaning1771 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1687 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1757 = false ∨ valuation q 1771 = true := counterClause1687 (baseVal q)

theorem counterClause1688 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1772 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1772)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 6 2 (meaning1738 q) (meaning1758 q) (meaning1772 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1688 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1758 = false ∨ valuation q 1772 = true := counterClause1688 (baseVal q)

theorem counterClause1689 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1773 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1773)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 6 3 (meaning1738 q) (meaning1759 q) (meaning1773 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1689 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1759 = false ∨ valuation q 1773 = true := counterClause1689 (baseVal q)

theorem counterClause1690 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1774 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1774)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 6 4 (meaning1738 q) (meaning1760 q) (meaning1774 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1690 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1760 = false ∨ valuation q 1774 = true := counterClause1690 (baseVal q)

theorem counterClause1691 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1775 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1775)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 6 5 (meaning1738 q) (meaning1761 q) (meaning1775 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1691 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1761 = false ∨ valuation q 1775 = true := counterClause1691 (baseVal q)

theorem counterClause1692 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1776 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1776)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 6 6 (meaning1738 q) (meaning1762 q) (meaning1776 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1692 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1762 = false ∨ valuation q 1776 = true := counterClause1692 (baseVal q)

theorem counterClause1693 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1775 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1775)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 7 4 (meaning1739 q) (meaning1760 q) (meaning1775 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1693 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1760 = false ∨ valuation q 1775 = true := counterClause1693 (baseVal q)

theorem counterClause1694 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1776 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1776)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 7 5 (meaning1739 q) (meaning1761 q) (meaning1776 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1694 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1761 = false ∨ valuation q 1776 = true := counterClause1694 (baseVal q)

theorem counterClause1695 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1781 = true := by
  have hs : count1781 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1781)) (countLit q [-99]) (countLit q [-100]) (count1781 q) 1 (meaningNeg100 q) (meaning1781 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1695 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1781 = true := counterClause1695 (baseVal q)

theorem counterClause1696 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1781 = true := by
  have hs : count1781 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1781)) (countLit q [-99]) (countLit q [-100]) (count1781 q) 1 (meaningNeg99 q) (meaning1781 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1696 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1781 = true := counterClause1696 (baseVal q)

theorem block52 (q : Snake 81) (h : Conditions q) : B112E055.Block52 (valuation q) :=
  ⟨clause1665 q h, clause1666 q h, clause1667 q h, clause1668 q h, clause1669 q h, clause1670 q h, clause1671 q h, clause1672 q h, clause1673 q h, clause1674 q h, clause1675 q h, clause1676 q h, clause1677 q h, clause1678 q h, clause1679 q h, clause1680 q h, clause1681 q h, clause1682 q h, clause1683 q h, clause1684 q h, clause1685 q h, clause1686 q h, clause1687 q h, clause1688 q h, clause1689 q h, clause1690 q h, clause1691 q h, clause1692 q h, clause1693 q h, clause1694 q h, clause1695 q h, clause1696 q h⟩

end
end Snake9.Regrowth.E112055
