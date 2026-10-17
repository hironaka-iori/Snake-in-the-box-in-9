import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec55 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1761 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 48 = false := by
  rw [value40, value42, value45, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (209 : Vertex) (213 : Vertex) (217 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1762 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value41, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (212 : Vertex) (213 : Vertex) (214 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1763 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value49, value51, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (259 : Vertex) (265 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1764 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 57 = false := by
  rw [value49, value53, value54, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (261 : Vertex) (265 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1765 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value50, value51, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (259 : Vertex) (274 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1766 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value52, value53, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (324 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1767 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value52, value53, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (388 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1768 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 70 = false ∨ valuation q 89 = false ∨ valuation q 113 = false := by
  rw [value53, value70, value89, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (325 : Vertex) (389 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1769 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 93 = false ∨ valuation q 95 = false := by
  rw [value54, value55, value93, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (265 : Vertex) (267 : Vertex) (393 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1770 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value56, value57, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (268 : Vertex) (269 : Vertex) (284 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1771 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value56, value58, value64, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (268 : Vertex) (270 : Vertex) (284 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1772 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 65 = false ∨ valuation q 96 = false ∨ valuation q 106 = false := by
  rw [value57, value65, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (269 : Vertex) (285 : Vertex) (397 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1773 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 66 = false ∨ valuation q 97 = false ∨ valuation q 107 = false := by
  rw [value58, value66, value97, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (270 : Vertex) (286 : Vertex) (398 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1774 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 67 = false ∨ valuation q 80 = false ∨ valuation q 85 = false := by
  rw [value62, value67, value80, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (279 : Vertex) (287 : Vertex) (343 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1775 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 67 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value62, value67, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (279 : Vertex) (287 : Vertex) (407 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1776 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 80 = false ∨ valuation q 102 = false ∨ valuation q 123 = false := by
  rw [value62, value80, value102, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (279 : Vertex) (343 : Vertex) (407 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1777 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value64, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (284 : Vertex) (285 : Vertex) (286 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1778 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value65, value67, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (285 : Vertex) (287 : Vertex) (413 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1779 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value66, value67, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (286 : Vertex) (287 : Vertex) (414 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1780 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value69, value70, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (324 : Vertex) (325 : Vertex) (326 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1781 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value69, value71, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (324 : Vertex) (326 : Vertex) (340 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1782 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 78 = false ∨ valuation q 80 = false := by
  rw [value70, value72, value78, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (325 : Vertex) (327 : Vertex) (341 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1783 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 79 = false ∨ valuation q 80 = false := by
  rw [value71, value72, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (326 : Vertex) (327 : Vertex) (342 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1784 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 80 = false ∨ valuation q 114 = false ∨ valuation q 123 = false := by
  rw [value72, value80, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (327 : Vertex) (343 : Vertex) (455 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1785 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 81 = false ∨ valuation q 83 = false := by
  rw [value73, value74, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (328 : Vertex) (330 : Vertex) (344 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1786 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value81, value82, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (344 : Vertex) (345 : Vertex) (346 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1787 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value86, value87, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1788 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 92 = false ∨ valuation q 94 = false := by
  rw [value86, value87, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (386 : Vertex) (392 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1789 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value88, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (388 : Vertex) (389 : Vertex) (390 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1790 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value88, value89, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (388 : Vertex) (389 : Vertex) (404 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1791 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value88, value90, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (388 : Vertex) (390 : Vertex) (404 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1792 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 100 = false ∨ valuation q 102 = false := by
  rw [value89, value91, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (389 : Vertex) (391 : Vertex) (405 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block55 (q : Snake 81) (h : Conditions q) : B112E050.Block55 (valuation q) :=
  ⟨clause1761 q h, clause1762 q h, clause1763 q h, clause1764 q h, clause1765 q h, clause1766 q h, clause1767 q h, clause1768 q h, clause1769 q h, clause1770 q h, clause1771 q h, clause1772 q h, clause1773 q h, clause1774 q h, clause1775 q h, clause1776 q h, clause1777 q h, clause1778 q h, clause1779 q h, clause1780 q h, clause1781 q h, clause1782 q h, clause1783 q h, clause1784 q h, clause1785 q h, clause1786 q h, clause1787 q h, clause1788 q h, clause1789 q h, clause1790 q h, clause1791 q h, clause1792 q h⟩

end
end Snake9.Regrowth.E112050
