import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec55 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1761 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 44 = false ∨ valuation q 45 = false := by
  rw [value40, value41, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (193 : Vertex) (200 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1762 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value40, value41, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (193 : Vertex) (448 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1763 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 44 = false ∨ valuation q 99 = false ∨ valuation q 105 = false := by
  rw [value40, value44, value99, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (200 : Vertex) (448 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1764 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value42, value43, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (198 : Vertex) (199 : Vertex) (214 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1765 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value44, value47, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (200 : Vertex) (204 : Vertex) (456 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1766 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value45, value46, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (201 : Vertex) (203 : Vertex) (217 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1767 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 56 = false ∨ valuation q 106 = false ∨ valuation q 118 = false := by
  rw [value46, value56, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (203 : Vertex) (219 : Vertex) (459 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1768 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value47, value48, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (206 : Vertex) (460 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1769 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 55 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value49, value55, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (210 : Vertex) (218 : Vertex) (466 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1770 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value50, value51, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (212 : Vertex) (213 : Vertex) (214 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1771 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value55, value56, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (218 : Vertex) (219 : Vertex) (474 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1772 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value62, value63, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (321 : Vertex) (448 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1773 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value62, value64, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (324 : Vertex) (328 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1774 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 99 = false ∨ valuation q 105 = false := by
  rw [value62, value66, value99, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (328 : Vertex) (448 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1775 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value64, value65, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (324 : Vertex) (326 : Vertex) (332 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1776 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 68 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value66, value68, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (328 : Vertex) (332 : Vertex) (456 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1777 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 77 = false ∨ valuation q 106 = false ∨ valuation q 118 = false := by
  rw [value67, value77, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (331 : Vertex) (347 : Vertex) (459 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1778 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value68, value69, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (332 : Vertex) (334 : Vertex) (460 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1779 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value79, value80, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (385 : Vertex) (388 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1780 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value79, value80, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (385 : Vertex) (448 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1781 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 83 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value80, value83, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (385 : Vertex) (389 : Vertex) (449 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1782 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value81, value84, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (390 : Vertex) (394 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1783 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 84 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value81, value84, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (390 : Vertex) (402 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1784 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 90 = false ∨ valuation q 101 = false ∨ valuation q 113 = false := by
  rw [value81, value90, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (402 : Vertex) (450 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1785 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 84 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value82, value84, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (388 : Vertex) (390 : Vertex) (396 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1786 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value85, value86, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (392 : Vertex) (394 : Vertex) (396 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1787 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 94 = false ∨ valuation q 105 = false ∨ valuation q 116 = false := by
  rw [value85, value94, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (392 : Vertex) (408 : Vertex) (456 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1788 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 96 = false ∨ valuation q 106 = false ∨ valuation q 118 = false := by
  rw [value87, value96, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (395 : Vertex) (411 : Vertex) (459 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1789 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 93 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value91, value93, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (405 : Vertex) (407 : Vertex) (413 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1790 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value95, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (409 : Vertex) (411 : Vertex) (413 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1791 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 98 = false ∨ valuation q 118 = false ∨ valuation q 121 = false := by
  rw [value96, value98, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (411 : Vertex) (415 : Vertex) (475 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1792 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value99, value100, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (448 : Vertex) (449 : Vertex) (464 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block55 (q : Snake 81) (h : Conditions q) : B112E019.Block55 (valuation q) :=
  ⟨clause1761 q h, clause1762 q h, clause1763 q h, clause1764 q h, clause1765 q h, clause1766 q h, clause1767 q h, clause1768 q h, clause1769 q h, clause1770 q h, clause1771 q h, clause1772 q h, clause1773 q h, clause1774 q h, clause1775 q h, clause1776 q h, clause1777 q h, clause1778 q h, clause1779 q h, clause1780 q h, clause1781 q h, clause1782 q h, clause1783 q h, clause1784 q h, clause1785 q h, clause1786 q h, clause1787 q h, clause1788 q h, clause1789 q h, clause1790 q h, clause1791 q h, clause1792 q h⟩

end
end Snake9.Regrowth.E112019
