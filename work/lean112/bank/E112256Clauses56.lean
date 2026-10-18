import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec56 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1793 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1766 = true := by
  have hs : count1765 q = (countLit q [-102, -104]) + (countLit q [-107, -110]) := List.countP_append (p := literal q) (l₁ := [-102, -104]) (l₂ := [-107, -110])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1766)) (countLit q [-102, -104]) (countLit q [-107, -110]) (count1765 q) 1 1 (meaning1761 q) (meaning1763 q) (meaning1766 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1793 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1763 = false ∨ valuation q 1766 = true := counterClause1793 (baseVal q)

theorem counterClause1794 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1771 = true := by
  have hs : count1769 q = (countLit q [-97, -98, -99, -100]) + (countLit q [-102, -104, -107, -110]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -99, -100]) (l₂ := [-102, -104, -107, -110])
  have hm := merge_two (literal (valuationOf q) (1757)) (literal (valuationOf q) (1766)) (literal (valuationOf q) (1771)) (countLit q [-97, -98, -99, -100]) (countLit q [-102, -104, -107, -110]) (count1769 q) 1 2 (meaning1757 q) (meaning1766 q) (meaning1771 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1794 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1766 = false ∨ valuation q 1771 = true := counterClause1794 (baseVal q)

theorem counterClause1795 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1779 = true := by
  have hs : count1779 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1779)) (countLit q [-115]) (countLit q [-117]) (count1779 q) 1 (meaningNeg115 q) (meaning1779 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1795 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1779 = true := counterClause1795 (baseVal q)

theorem counterClause1796 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1781 = true := by
  have hs : count1781 q = (countLit q [-112, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1779)) (literal (valuationOf q) (1781)) (countLit q [-112, -114]) (countLit q [-115, -117]) (count1781 q) 1 (meaning1779 q) (meaning1781 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1796 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1781 = true := counterClause1796 (baseVal q)

theorem counterClause1797 (q : Nat → Bool) : valuationOf q 1781 = false ∨ valuationOf q 1797 = true := by
  have hs : count1797 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-119, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-119, -121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1781)) (literal (valuationOf q) (1797)) (countLit q [-112, -114, -115, -117]) (countLit q [-119, -121, -123, -125, -127]) (count1797 q) 1 (meaning1781 q) (meaning1797 q) hs
  change valuationOf q 1781 = false ∨ valuationOf q 1797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1797 (q : Snake 81) (h : Conditions q) : valuation q 1781 = false ∨ valuation q 1797 = true := counterClause1797 (baseVal q)

theorem counterClause1798 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1809 = true := by
  have hs : count1806 q = (countLit q [-97, -98, -99, -100, -102, -104, -107, -110]) + (countLit q [-112, -114, -115, -117, -119, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -99, -100, -102, -104, -107, -110]) (l₂ := [-112, -114, -115, -117, -119, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1797)) (literal (valuationOf q) (1809)) (countLit q [-97, -98, -99, -100, -102, -104, -107, -110]) (countLit q [-112, -114, -115, -117, -119, -121, -123, -125, -127]) (count1806 q) 3 1 (meaning1771 q) (meaning1797 q) (meaning1809 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1798 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1797 = false ∨ valuation q 1809 = true := counterClause1798 (baseVal q)

theorem counterClause1799 (q : Nat → Bool) : valuationOf q 1743 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1833 = true := by
  have hs : count1823 q = (countLit q [-69, -71, -72, -73, -75, -77, -80, -81, -82, -85, -86, -87, -89, -92, -94, -95]) + (countLit q [-97, -98, -99, -100, -102, -104, -107, -110, -112, -114, -115, -117, -119, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -72, -73, -75, -77, -80, -81, -82, -85, -86, -87, -89, -92, -94, -95]) (l₂ := [-97, -98, -99, -100, -102, -104, -107, -110, -112, -114, -115, -117, -119, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1743)) (literal (valuationOf q) (1809)) (literal (valuationOf q) (1833)) (countLit q [-69, -71, -72, -73, -75, -77, -80, -81, -82, -85, -86, -87, -89, -92, -94, -95]) (countLit q [-97, -98, -99, -100, -102, -104, -107, -110, -112, -114, -115, -117, -119, -121, -123, -125, -127]) (count1823 q) 7 4 (meaning1743 q) (meaning1809 q) (meaning1833 q) hs
  change valuationOf q 1743 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1799 (q : Snake 81) (h : Conditions q) : valuation q 1743 = false ∨ valuation q 1809 = false ∨ valuation q 1833 = true := counterClause1799 (baseVal q)

theorem counterClause1800 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1874 = true := by
  have hs : count1849 q = (countLit q [-3, -4, -6, -8, -9, -12, -13, -16, -17, -20, -22, -24, -26, -27, -29, -31, -32, -35, -37, -38, -39, -40, -46, -48, -50, -51, -52, -54, -55, -56, -59, -64, -66]) + (countLit q [-69, -71, -72, -73, -75, -77, -80, -81, -82, -85, -86, -87, -89, -92, -94, -95, -97, -98, -99, -100, -102, -104, -107, -110, -112, -114, -115, -117, -119, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -9, -12, -13, -16, -17, -20, -22, -24, -26, -27, -29, -31, -32, -35, -37, -38, -39, -40, -46, -48, -50, -51, -52, -54, -55, -56, -59, -64, -66]) (l₂ := [-69, -71, -72, -73, -75, -77, -80, -81, -82, -85, -86, -87, -89, -92, -94, -95, -97, -98, -99, -100, -102, -104, -107, -110, -112, -114, -115, -117, -119, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1874)) (countLit q [-3, -4, -6, -8, -9, -12, -13, -16, -17, -20, -22, -24, -26, -27, -29, -31, -32, -35, -37, -38, -39, -40, -46, -48, -50, -51, -52, -54, -55, -56, -59, -64, -66]) (countLit q [-69, -71, -72, -73, -75, -77, -80, -81, -82, -85, -86, -87, -89, -92, -94, -95, -97, -98, -99, -100, -102, -104, -107, -110, -112, -114, -115, -117, -119, -121, -123, -125, -127]) (count1849 q) 15 11 (meaning1677 q) (meaning1833 q) (meaning1874 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1800 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1833 = false ∨ valuation q 1874 = true := counterClause1800 (baseVal q)

theorem clause1801 (q : Snake 81) (h : Conditions q) : valuation q 1874 = false := by
  rw [value1874]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1849 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1802 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 37 = false ∨ valuation q 41 = false := by
  rw [value1, value6, value37, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (65 : Vertex) (73 : Vertex) (193 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1803 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 40 = false ∨ valuation q 43 = false := by
  rw [value5, value8, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (72 : Vertex) (76 : Vertex) (200 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1804 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value6, value7, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (73 : Vertex) (75 : Vertex) (105 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1805 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 41 = false ∨ valuation q 50 = false := by
  rw [value6, value14, value41, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (73 : Vertex) (89 : Vertex) (201 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1806 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 78 = false ∨ valuation q 87 = false := by
  rw [value6, value14, value78, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (73 : Vertex) (89 : Vertex) (329 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1807 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 18 = false ∨ valuation q 44 = false ∨ valuation q 54 = false := by
  rw [value9, value18, value44, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (79 : Vertex) (95 : Vertex) (207 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1808 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 46 = false ∨ valuation q 49 = false := by
  rw [value11, value13, value46, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (83 : Vertex) (87 : Vertex) (211 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1809 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 29 = false ∨ valuation q 46 = false ∨ valuation q 65 = false := by
  rw [value11, value29, value46, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (83 : Vertex) (115 : Vertex) (211 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1810 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 30 = false ∨ valuation q 47 = false ∨ valuation q 66 = false := by
  rw [value12, value30, value47, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (84 : Vertex) (116 : Vertex) (212 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1811 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 49 = false ∨ valuation q 54 = false := by
  rw [value13, value18, value49, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (87 : Vertex) (95 : Vertex) (215 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1812 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value14, value16, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (89 : Vertex) (93 : Vertex) (345 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1813 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 50 = false ∨ valuation q 87 = false ∨ valuation q 111 = false := by
  rw [value14, value50, value87, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (89 : Vertex) (217 : Vertex) (345 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1814 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value15, value17, value32, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (90 : Vertex) (94 : Vertex) (122 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1815 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 32 = false ∨ valuation q 51 = false ∨ valuation q 70 = false := by
  rw [value15, value32, value51, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (90 : Vertex) (122 : Vertex) (218 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1816 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 33 = false ∨ valuation q 53 = false ∨ valuation q 72 = false := by
  rw [value16, value33, value53, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (93 : Vertex) (125 : Vertex) (221 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1817 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 27 = false ∨ valuation q 55 = false ∨ valuation q 63 = false := by
  rw [value19, value27, value55, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (96 : Vertex) (112 : Vertex) (224 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1818 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 34 = false ∨ valuation q 62 = false ∨ valuation q 73 = false := by
  rw [value26, value34, value62, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (110 : Vertex) (126 : Vertex) (238 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1819 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 63 = false ∨ valuation q 64 = false := by
  rw [value27, value28, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (112 : Vertex) (113 : Vertex) (240 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1820 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value28, value29, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (113 : Vertex) (115 : Vertex) (241 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1821 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value30, value31, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (116 : Vertex) (118 : Vertex) (244 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1822 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 68 = false ∨ valuation q 73 = false := by
  rw [value31, value34, value68, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (118 : Vertex) (126 : Vertex) (246 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1823 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 72 = false ∨ valuation q 99 = false ∨ valuation q 126 = false := by
  rw [value33, value72, value99, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (125 : Vertex) (253 : Vertex) (381 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1824 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 39 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value36, value39, value55, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (196 : Vertex) (224 : Vertex) (228 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block56 (q : Snake 81) (h : Conditions q) : B112E256.Block56 (valuation q) :=
  ⟨clause1793 q h, clause1794 q h, clause1795 q h, clause1796 q h, clause1797 q h, clause1798 q h, clause1799 q h, clause1800 q h, clause1801 q h, clause1802 q h, clause1803 q h, clause1804 q h, clause1805 q h, clause1806 q h, clause1807 q h, clause1808 q h, clause1809 q h, clause1810 q h, clause1811 q h, clause1812 q h, clause1813 q h, clause1814 q h, clause1815 q h, clause1816 q h, clause1817 q h, clause1818 q h, clause1819 q h, clause1820 q h, clause1821 q h, clause1822 q h, clause1823 q h, clause1824 q h⟩

end
end Snake9.Regrowth.E112256
