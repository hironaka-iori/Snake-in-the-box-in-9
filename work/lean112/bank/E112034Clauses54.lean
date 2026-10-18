import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec54 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1729 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 43 = false ∨ valuation q 108 = false ∨ valuation q 120 = false := by
  rw [value33, value43, value108, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (227 : Vertex) (243 : Vertex) (483 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1730 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 109 = false ∨ valuation q 110 = false := by
  rw [value34, value35, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (229 : Vertex) (484 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1731 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 39 = false ∨ valuation q 110 = false ∨ valuation q 117 = false := by
  rw [value35, value39, value110, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (229 : Vertex) (237 : Vertex) (485 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1732 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value36, value38, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (233 : Vertex) (235 : Vertex) (237 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1733 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 39 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value36, value39, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (233 : Vertex) (237 : Vertex) (489 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1734 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value41, value44, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (240 : Vertex) (244 : Vertex) (248 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1735 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 119 = false ∨ valuation q 120 = false := by
  rw [value42, value43, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (241 : Vertex) (243 : Vertex) (497 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1736 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value44, value45, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (244 : Vertex) (246 : Vertex) (252 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1737 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 57 = false ∨ valuation q 69 = false ∨ valuation q 74 = false := by
  rw [value52, value57, value69, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (290 : Vertex) (298 : Vertex) (354 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1738 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value53, value54, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (292 : Vertex) (293 : Vertex) (356 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1739 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value57, value58, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (298 : Vertex) (299 : Vertex) (362 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1740 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 74 = false ∨ valuation q 93 = false ∨ valuation q 115 = false := by
  rw [value57, value74, value93, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (298 : Vertex) (362 : Vertex) (426 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1741 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value61, value63, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (309 : Vertex) (311 : Vertex) (317 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1742 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value65, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (313 : Vertex) (315 : Vertex) (317 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1743 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value69, value70, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (354 : Vertex) (355 : Vertex) (362 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1744 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 74 = false ∨ valuation q 107 = false ∨ valuation q 115 = false := by
  rw [value69, value74, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (354 : Vertex) (362 : Vertex) (482 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1745 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value73, value75, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (361 : Vertex) (363 : Vertex) (365 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1746 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 76 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value73, value76, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (361 : Vertex) (365 : Vertex) (489 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1747 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value78, value81, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (368 : Vertex) (372 : Vertex) (376 : Vertex) (380 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1748 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 119 = false ∨ valuation q 120 = false := by
  rw [value79, value80, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (369 : Vertex) (371 : Vertex) (497 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1749 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value86, value87, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (417 : Vertex) (432 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1750 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value86, value88, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (418 : Vertex) (432 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1751 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value86, value90, value96, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (420 : Vertex) (432 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1752 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 97 = false ∨ valuation q 99 = false := by
  rw [value87, value89, value97, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (417 : Vertex) (419 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1753 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value88, value89, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (418 : Vertex) (419 : Vertex) (434 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1754 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value88, value93, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (418 : Vertex) (426 : Vertex) (434 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1755 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 93 = false ∨ valuation q 107 = false ∨ valuation q 115 = false := by
  rw [value88, value93, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (418 : Vertex) (426 : Vertex) (482 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1756 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 108 = false ∨ valuation q 112 = false := by
  rw [value89, value91, value108, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (419 : Vertex) (423 : Vertex) (483 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1757 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 108 = false ∨ valuation q 120 = false := by
  rw [value89, value99, value108, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (419 : Vertex) (435 : Vertex) (483 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1758 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 94 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value92, value94, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (425 : Vertex) (429 : Vertex) (489 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1759 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 101 = false ∨ valuation q 115 = false ∨ valuation q 126 = false := by
  rw [value93, value101, value115, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (426 : Vertex) (442 : Vertex) (490 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1760 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 103 = false ∨ valuation q 105 = false := by
  rw [value94, value95, value103, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (429 : Vertex) (431 : Vertex) (445 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block54 (q : Snake 81) (h : Conditions q) : B112E034.Block54 (valuation q) :=
  ⟨clause1729 q h, clause1730 q h, clause1731 q h, clause1732 q h, clause1733 q h, clause1734 q h, clause1735 q h, clause1736 q h, clause1737 q h, clause1738 q h, clause1739 q h, clause1740 q h, clause1741 q h, clause1742 q h, clause1743 q h, clause1744 q h, clause1745 q h, clause1746 q h, clause1747 q h, clause1748 q h, clause1749 q h, clause1750 q h, clause1751 q h, clause1752 q h, clause1753 q h, clause1754 q h, clause1755 q h, clause1756 q h, clause1757 q h, clause1758 q h, clause1759 q h, clause1760 q h⟩

end
end Snake9.Regrowth.E112034
