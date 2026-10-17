import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec63 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause2017 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1772 = true := by
  have hs : count1769 q = (countLit q [-95, -97, -99, -101]) + (countLit q [-102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -99, -101]) (l₂ := [-102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1767)) (literal (valuationOf q) (1772)) (countLit q [-95, -97, -99, -101]) (countLit q [-102, -104, -106, -107]) (count1769 q) 1 3 (meaning1757 q) (meaning1767 q) (meaning1772 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2017 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1767 = false ∨ valuation q 1772 = true := counterClause2017 (baseVal q)

theorem counterClause2018 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1771 = true := by
  have hs : count1769 q = (countLit q [-95, -97, -99, -101]) + (countLit q [-102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -99, -101]) (l₂ := [-102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1771)) (countLit q [-95, -97, -99, -101]) (countLit q [-102, -104, -106, -107]) (count1769 q) 2 1 (meaning1758 q) (meaning1765 q) (meaning1771 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2018 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1765 = false ∨ valuation q 1771 = true := counterClause2018 (baseVal q)

theorem counterClause2019 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1772 = true := by
  have hs : count1769 q = (countLit q [-95, -97, -99, -101]) + (countLit q [-102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -99, -101]) (l₂ := [-102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1766)) (literal (valuationOf q) (1772)) (countLit q [-95, -97, -99, -101]) (countLit q [-102, -104, -106, -107]) (count1769 q) 2 2 (meaning1758 q) (meaning1766 q) (meaning1772 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2019 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1766 = false ∨ valuation q 1772 = true := counterClause2019 (baseVal q)

theorem counterClause2020 (q : Nat → Bool) : valuationOf q 1758 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1773 = true := by
  have hs : count1769 q = (countLit q [-95, -97, -99, -101]) + (countLit q [-102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -99, -101]) (l₂ := [-102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1758)) (literal (valuationOf q) (1767)) (literal (valuationOf q) (1773)) (countLit q [-95, -97, -99, -101]) (countLit q [-102, -104, -106, -107]) (count1769 q) 2 3 (meaning1758 q) (meaning1767 q) (meaning1773 q) hs
  change valuationOf q 1758 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2020 (q : Snake 81) (h : Conditions q) : valuation q 1758 = false ∨ valuation q 1767 = false ∨ valuation q 1773 = true := counterClause2020 (baseVal q)

theorem counterClause2021 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1777 = true := by
  have hs : count1777 q = (countLit q [-109]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-112])
  have hm := merge_left (literal (valuationOf q) (-109)) (literal (valuationOf q) (1777)) (countLit q [-109]) (countLit q [-112]) (count1777 q) 1 (meaningNeg109 q) (meaning1777 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1777 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2021 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1777 = true := counterClause2021 (baseVal q)

theorem counterClause2022 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1779 = true := by
  have hs : count1779 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_right (literal (valuationOf q) (-116)) (literal (valuationOf q) (1779)) (countLit q [-114]) (countLit q [-116]) (count1779 q) 1 (meaningNeg116 q) (meaning1779 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2022 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1779 = true := counterClause2022 (baseVal q)

theorem counterClause2023 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 116 = true ∨ valuationOf q 1780 = true := by
  have hs : count1779 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_two (literal (valuationOf q) (-114)) (literal (valuationOf q) (-116)) (literal (valuationOf q) (1780)) (countLit q [-114]) (countLit q [-116]) (count1779 q) 1 1 (meaningNeg114 q) (meaningNeg116 q) (meaning1780 q) hs
  change (! (valuationOf q 114)) = false ∨ (! (valuationOf q 116)) = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2023 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 116 = true ∨ valuation q 1780 = true := counterClause2023 (baseVal q)

theorem counterClause2024 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1781 = true := by
  have hs : count1781 q = (countLit q [-109, -112]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-114, -116])
  have hm := merge_right (literal (valuationOf q) (1779)) (literal (valuationOf q) (1781)) (countLit q [-109, -112]) (countLit q [-114, -116]) (count1781 q) 1 (meaning1779 q) (meaning1781 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2024 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1781 = true := counterClause2024 (baseVal q)

theorem counterClause2025 (q : Nat → Bool) : valuationOf q 1780 = false ∨ valuationOf q 1782 = true := by
  have hs : count1781 q = (countLit q [-109, -112]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-114, -116])
  have hm := merge_right (literal (valuationOf q) (1780)) (literal (valuationOf q) (1782)) (countLit q [-109, -112]) (countLit q [-114, -116]) (count1781 q) 2 (meaning1780 q) (meaning1782 q) hs
  change valuationOf q 1780 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2025 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false ∨ valuation q 1782 = true := counterClause2025 (baseVal q)

theorem counterClause2026 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1781 = true := by
  have hs : count1781 q = (countLit q [-109, -112]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-114, -116])
  have hm := merge_left (literal (valuationOf q) (1777)) (literal (valuationOf q) (1781)) (countLit q [-109, -112]) (countLit q [-114, -116]) (count1781 q) 1 (meaning1777 q) (meaning1781 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2026 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1781 = true := counterClause2026 (baseVal q)

theorem counterClause2027 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1779 = false ∨ valuationOf q 1782 = true := by
  have hs : count1781 q = (countLit q [-109, -112]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-114, -116])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1779)) (literal (valuationOf q) (1782)) (countLit q [-109, -112]) (countLit q [-114, -116]) (count1781 q) 1 1 (meaning1777 q) (meaning1779 q) (meaning1782 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1779 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2027 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1779 = false ∨ valuation q 1782 = true := counterClause2027 (baseVal q)

theorem counterClause2028 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 1785 = true := by
  have hs : count1785 q = (countLit q [-118]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-120])
  have hm := merge_right (literal (valuationOf q) (-120)) (literal (valuationOf q) (1785)) (countLit q [-118]) (countLit q [-120]) (count1785 q) 1 (meaningNeg120 q) (meaning1785 q) hs
  change (! (valuationOf q 120)) = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2028 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 1785 = true := counterClause2028 (baseVal q)

theorem counterClause2029 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1785 = true := by
  have hs : count1785 q = (countLit q [-118]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-120])
  have hm := merge_left (literal (valuationOf q) (-118)) (literal (valuationOf q) (1785)) (countLit q [-118]) (countLit q [-120]) (count1785 q) 1 (meaningNeg118 q) (meaning1785 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2029 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1785 = true := counterClause2029 (baseVal q)

theorem counterClause2030 (q : Nat → Bool) : valuationOf q 125 = true ∨ valuationOf q 1787 = true := by
  have hs : count1787 q = (countLit q [-123]) + (countLit q [-125]) := List.countP_append (p := literal q) (l₁ := [-123]) (l₂ := [-125])
  have hm := merge_right (literal (valuationOf q) (-125)) (literal (valuationOf q) (1787)) (countLit q [-123]) (countLit q [-125]) (count1787 q) 1 (meaningNeg125 q) (meaning1787 q) hs
  change (! (valuationOf q 125)) = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2030 (q : Snake 81) (h : Conditions q) : valuation q 125 = true ∨ valuation q 1787 = true := counterClause2030 (baseVal q)

theorem counterClause2031 (q : Nat → Bool) : valuationOf q 123 = true ∨ valuationOf q 125 = true ∨ valuationOf q 1788 = true := by
  have hs : count1787 q = (countLit q [-123]) + (countLit q [-125]) := List.countP_append (p := literal q) (l₁ := [-123]) (l₂ := [-125])
  have hm := merge_two (literal (valuationOf q) (-123)) (literal (valuationOf q) (-125)) (literal (valuationOf q) (1788)) (countLit q [-123]) (countLit q [-125]) (count1787 q) 1 1 (meaningNeg123 q) (meaningNeg125 q) (meaning1788 q) hs
  change (! (valuationOf q 123)) = false ∨ (! (valuationOf q 125)) = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2031 (q : Snake 81) (h : Conditions q) : valuation q 123 = true ∨ valuation q 125 = true ∨ valuation q 1788 = true := counterClause2031 (baseVal q)

theorem counterClause2032 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1789 = true := by
  have hs : count1789 q = (countLit q [-121]) + (countLit q [-123, -125]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123, -125])
  have hm := merge_right (literal (valuationOf q) (1787)) (literal (valuationOf q) (1789)) (countLit q [-121]) (countLit q [-123, -125]) (count1789 q) 1 (meaning1787 q) (meaning1789 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2032 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1789 = true := counterClause2032 (baseVal q)

theorem counterClause2033 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1790 = true := by
  have hs : count1789 q = (countLit q [-121]) + (countLit q [-123, -125]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123, -125])
  have hm := merge_right (literal (valuationOf q) (1788)) (literal (valuationOf q) (1790)) (countLit q [-121]) (countLit q [-123, -125]) (count1789 q) 2 (meaning1788 q) (meaning1790 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2033 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1790 = true := counterClause2033 (baseVal q)

theorem counterClause2034 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 1789 = true := by
  have hs : count1789 q = (countLit q [-121]) + (countLit q [-123, -125]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123, -125])
  have hm := merge_left (literal (valuationOf q) (-121)) (literal (valuationOf q) (1789)) (countLit q [-121]) (countLit q [-123, -125]) (count1789 q) 1 (meaningNeg121 q) (meaning1789 q) hs
  change (! (valuationOf q 121)) = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2034 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 1789 = true := counterClause2034 (baseVal q)

theorem counterClause2035 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1792 = true := by
  have hs : count1792 q = (countLit q [-118, -120]) + (countLit q [-121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-118, -120]) (l₂ := [-121, -123, -125])
  have hm := merge_right (literal (valuationOf q) (1789)) (literal (valuationOf q) (1792)) (countLit q [-118, -120]) (countLit q [-121, -123, -125]) (count1792 q) 1 (meaning1789 q) (meaning1792 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2035 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1792 = true := counterClause2035 (baseVal q)

theorem counterClause2036 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1793 = true := by
  have hs : count1792 q = (countLit q [-118, -120]) + (countLit q [-121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-118, -120]) (l₂ := [-121, -123, -125])
  have hm := merge_right (literal (valuationOf q) (1790)) (literal (valuationOf q) (1793)) (countLit q [-118, -120]) (countLit q [-121, -123, -125]) (count1792 q) 2 (meaning1790 q) (meaning1793 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2036 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1793 = true := counterClause2036 (baseVal q)

theorem counterClause2037 (q : Nat → Bool) : valuationOf q 1785 = false ∨ valuationOf q 1792 = true := by
  have hs : count1792 q = (countLit q [-118, -120]) + (countLit q [-121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-118, -120]) (l₂ := [-121, -123, -125])
  have hm := merge_left (literal (valuationOf q) (1785)) (literal (valuationOf q) (1792)) (countLit q [-118, -120]) (countLit q [-121, -123, -125]) (count1792 q) 1 (meaning1785 q) (meaning1792 q) hs
  change valuationOf q 1785 = false ∨ valuationOf q 1792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2037 (q : Snake 81) (h : Conditions q) : valuation q 1785 = false ∨ valuation q 1792 = true := counterClause2037 (baseVal q)

theorem counterClause2038 (q : Nat → Bool) : valuationOf q 1785 = false ∨ valuationOf q 1789 = false ∨ valuationOf q 1793 = true := by
  have hs : count1792 q = (countLit q [-118, -120]) + (countLit q [-121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-118, -120]) (l₂ := [-121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1785)) (literal (valuationOf q) (1789)) (literal (valuationOf q) (1793)) (countLit q [-118, -120]) (countLit q [-121, -123, -125]) (count1792 q) 1 1 (meaning1785 q) (meaning1789 q) (meaning1793 q) hs
  change valuationOf q 1785 = false ∨ valuationOf q 1789 = false ∨ valuationOf q 1793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2038 (q : Snake 81) (h : Conditions q) : valuation q 1785 = false ∨ valuation q 1789 = false ∨ valuation q 1793 = true := counterClause2038 (baseVal q)

theorem counterClause2039 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1797 = true := by
  have hs : count1797 q = (countLit q [-109, -112, -114, -116]) + (countLit q [-118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -114, -116]) (l₂ := [-118, -120, -121, -123, -125])
  have hm := merge_right (literal (valuationOf q) (1792)) (literal (valuationOf q) (1797)) (countLit q [-109, -112, -114, -116]) (countLit q [-118, -120, -121, -123, -125]) (count1797 q) 1 (meaning1792 q) (meaning1797 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2039 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1797 = true := counterClause2039 (baseVal q)

theorem counterClause2040 (q : Nat → Bool) : valuationOf q 1781 = false ∨ valuationOf q 1792 = false ∨ valuationOf q 1798 = true := by
  have hs : count1797 q = (countLit q [-109, -112, -114, -116]) + (countLit q [-118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -114, -116]) (l₂ := [-118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1781)) (literal (valuationOf q) (1792)) (literal (valuationOf q) (1798)) (countLit q [-109, -112, -114, -116]) (countLit q [-118, -120, -121, -123, -125]) (count1797 q) 1 1 (meaning1781 q) (meaning1792 q) (meaning1798 q) hs
  change valuationOf q 1781 = false ∨ valuationOf q 1792 = false ∨ valuationOf q 1798 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2040 (q : Snake 81) (h : Conditions q) : valuation q 1781 = false ∨ valuation q 1792 = false ∨ valuation q 1798 = true := counterClause2040 (baseVal q)

theorem counterClause2041 (q : Nat → Bool) : valuationOf q 1781 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1799 = true := by
  have hs : count1797 q = (countLit q [-109, -112, -114, -116]) + (countLit q [-118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -114, -116]) (l₂ := [-118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1781)) (literal (valuationOf q) (1793)) (literal (valuationOf q) (1799)) (countLit q [-109, -112, -114, -116]) (countLit q [-118, -120, -121, -123, -125]) (count1797 q) 1 2 (meaning1781 q) (meaning1793 q) (meaning1799 q) hs
  change valuationOf q 1781 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2041 (q : Snake 81) (h : Conditions q) : valuation q 1781 = false ∨ valuation q 1793 = false ∨ valuation q 1799 = true := counterClause2041 (baseVal q)

theorem counterClause2042 (q : Nat → Bool) : valuationOf q 1782 = false ∨ valuationOf q 1792 = false ∨ valuationOf q 1799 = true := by
  have hs : count1797 q = (countLit q [-109, -112, -114, -116]) + (countLit q [-118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -114, -116]) (l₂ := [-118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1782)) (literal (valuationOf q) (1792)) (literal (valuationOf q) (1799)) (countLit q [-109, -112, -114, -116]) (countLit q [-118, -120, -121, -123, -125]) (count1797 q) 2 1 (meaning1782 q) (meaning1792 q) (meaning1799 q) hs
  change valuationOf q 1782 = false ∨ valuationOf q 1792 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2042 (q : Snake 81) (h : Conditions q) : valuation q 1782 = false ∨ valuation q 1792 = false ∨ valuation q 1799 = true := counterClause2042 (baseVal q)

theorem counterClause2043 (q : Nat → Bool) : valuationOf q 1782 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1800 = true := by
  have hs : count1797 q = (countLit q [-109, -112, -114, -116]) + (countLit q [-118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -114, -116]) (l₂ := [-118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1782)) (literal (valuationOf q) (1793)) (literal (valuationOf q) (1800)) (countLit q [-109, -112, -114, -116]) (countLit q [-118, -120, -121, -123, -125]) (count1797 q) 2 2 (meaning1782 q) (meaning1793 q) (meaning1800 q) hs
  change valuationOf q 1782 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2043 (q : Snake 81) (h : Conditions q) : valuation q 1782 = false ∨ valuation q 1793 = false ∨ valuation q 1800 = true := counterClause2043 (baseVal q)

theorem counterClause2044 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1809 = true := by
  have hs : count1806 q = (countLit q [-95, -97, -99, -101, -102, -104, -106, -107]) + (countLit q [-109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -99, -101, -102, -104, -106, -107]) (l₂ := [-109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1797)) (literal (valuationOf q) (1809)) (countLit q [-95, -97, -99, -101, -102, -104, -106, -107]) (countLit q [-109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1806 q) 3 1 (meaning1771 q) (meaning1797 q) (meaning1809 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2044 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1797 = false ∨ valuation q 1809 = true := counterClause2044 (baseVal q)

theorem counterClause2045 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1811 = true := by
  have hs : count1806 q = (countLit q [-95, -97, -99, -101, -102, -104, -106, -107]) + (countLit q [-109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -99, -101, -102, -104, -106, -107]) (l₂ := [-109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1799)) (literal (valuationOf q) (1811)) (countLit q [-95, -97, -99, -101, -102, -104, -106, -107]) (countLit q [-109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1806 q) 3 3 (meaning1771 q) (meaning1799 q) (meaning1811 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2045 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1799 = false ∨ valuation q 1811 = true := counterClause2045 (baseVal q)

theorem counterClause2046 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1811 = true := by
  have hs : count1806 q = (countLit q [-95, -97, -99, -101, -102, -104, -106, -107]) + (countLit q [-109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -99, -101, -102, -104, -106, -107]) (l₂ := [-109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1798)) (literal (valuationOf q) (1811)) (countLit q [-95, -97, -99, -101, -102, -104, -106, -107]) (countLit q [-109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1806 q) 4 2 (meaning1772 q) (meaning1798 q) (meaning1811 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2046 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1798 = false ∨ valuation q 1811 = true := counterClause2046 (baseVal q)

theorem counterClause2047 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1812 = true := by
  have hs : count1806 q = (countLit q [-95, -97, -99, -101, -102, -104, -106, -107]) + (countLit q [-109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -99, -101, -102, -104, -106, -107]) (l₂ := [-109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1799)) (literal (valuationOf q) (1812)) (countLit q [-95, -97, -99, -101, -102, -104, -106, -107]) (countLit q [-109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1806 q) 4 3 (meaning1772 q) (meaning1799 q) (meaning1812 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2047 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1799 = false ∨ valuation q 1812 = true := counterClause2047 (baseVal q)

theorem counterClause2048 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1813 = true := by
  have hs : count1806 q = (countLit q [-95, -97, -99, -101, -102, -104, -106, -107]) + (countLit q [-109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -99, -101, -102, -104, -106, -107]) (l₂ := [-109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1800)) (literal (valuationOf q) (1813)) (countLit q [-95, -97, -99, -101, -102, -104, -106, -107]) (countLit q [-109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1806 q) 4 4 (meaning1772 q) (meaning1800 q) (meaning1813 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2048 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1800 = false ∨ valuation q 1813 = true := counterClause2048 (baseVal q)

theorem block63 (q : Snake 81) (h : Conditions q) : B112E260.Block63 (valuation q) :=
  ⟨clause2017 q h, clause2018 q h, clause2019 q h, clause2020 q h, clause2021 q h, clause2022 q h, clause2023 q h, clause2024 q h, clause2025 q h, clause2026 q h, clause2027 q h, clause2028 q h, clause2029 q h, clause2030 q h, clause2031 q h, clause2032 q h, clause2033 q h, clause2034 q h, clause2035 q h, clause2036 q h, clause2037 q h, clause2038 q h, clause2039 q h, clause2040 q h, clause2041 q h, clause2042 q h, clause2043 q h, clause2044 q h, clause2045 q h, clause2046 q h, clause2047 q h, clause2048 q h⟩

end
end Snake9.Regrowth.E112260
