import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec52 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1665 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 12 = false ∨ valuation q 20 = false ∨ valuation q 24 = false := by
  rw [value9, value12, value20, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (33 : Vertex) (37 : Vertex) (49 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1666 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 16 = false ∨ valuation q 20 = false ∨ valuation q 27 = false := by
  rw [value9, value16, value20, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (33 : Vertex) (41 : Vertex) (49 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1667 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 20 = false ∨ valuation q 70 = false ∨ valuation q 78 = false := by
  rw [value9, value20, value70, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (33 : Vertex) (49 : Vertex) (289 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1668 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 13 = false ∨ valuation q 17 = false ∨ valuation q 19 = false := by
  rw [value10, value13, value17, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (34 : Vertex) (38 : Vertex) (42 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1669 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 25 = false := by
  rw [value10, value13, value21, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (34 : Vertex) (38 : Vertex) (50 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1670 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 28 = false := by
  rw [value10, value17, value21, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (34 : Vertex) (42 : Vertex) (50 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1671 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value11, value12, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (36 : Vertex) (37 : Vertex) (38 : Vertex) (39 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1672 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value11, value12, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (36 : Vertex) (37 : Vertex) (52 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1673 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 19 = false := by
  rw [value11, value13, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (36 : Vertex) (38 : Vertex) (44 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1674 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 23 = false ∨ valuation q 25 = false := by
  rw [value11, value13, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (36 : Vertex) (38 : Vertex) (52 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1675 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value12, value14, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (37 : Vertex) (39 : Vertex) (53 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1676 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value13, value14, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (38 : Vertex) (39 : Vertex) (54 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1677 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value13, value14, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (38 : Vertex) (39 : Vertex) (294 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1678 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 30 = false := by
  rw [value13, value19, value25, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (38 : Vertex) (46 : Vertex) (54 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1679 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 25 = false ∨ valuation q 47 = false ∨ valuation q 56 = false := by
  rw [value13, value25, value47, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (38 : Vertex) (54 : Vertex) (166 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1680 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 25 = false ∨ valuation q 71 = false ∨ valuation q 82 = false := by
  rw [value13, value25, value71, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (38 : Vertex) (54 : Vertex) (294 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1681 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 47 = false ∨ valuation q 71 = false ∨ valuation q 92 = false := by
  rw [value13, value47, value71, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (38 : Vertex) (166 : Vertex) (294 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1682 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 19 = false := by
  rw [value15, value17, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (40 : Vertex) (42 : Vertex) (44 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1683 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 30 = false := by
  rw [value17, value19, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (42 : Vertex) (46 : Vertex) (58 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1684 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value20, value22, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (49 : Vertex) (51 : Vertex) (53 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1685 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 27 = false ∨ valuation q 29 = false := by
  rw [value20, value22, value27, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (49 : Vertex) (51 : Vertex) (57 : Vertex) (59 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1686 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value20, value22, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (49 : Vertex) (51 : Vertex) (177 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1687 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 78 = false ∨ valuation q 80 = false := by
  rw [value20, value22, value78, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (49 : Vertex) (51 : Vertex) (305 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1688 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 53 = false ∨ valuation q 78 = false ∨ valuation q 100 = false := by
  rw [value20, value53, value78, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (49 : Vertex) (177 : Vertex) (305 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1689 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 79 = false ∨ valuation q 80 = false := by
  rw [value21, value22, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (50 : Vertex) (51 : Vertex) (306 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1690 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 25 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value21, value25, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (50 : Vertex) (54 : Vertex) (178 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1691 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 28 = false ∨ valuation q 79 = false ∨ valuation q 83 = false := by
  rw [value21, value28, value79, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (50 : Vertex) (58 : Vertex) (306 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1692 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value23, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (52 : Vertex) (53 : Vertex) (54 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1693 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value28, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (58 : Vertex) (59 : Vertex) (62 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1694 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value44, value45, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1695 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 57 = false := by
  rw [value44, value48, value52, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (176 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1696 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 48 = false ∨ valuation q 87 = false ∨ valuation q 94 = false := by
  rw [value44, value48, value87, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (416 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block52 (q : Snake 81) (h : Conditions q) : B112E121.Block52 (valuation q) :=
  ⟨clause1665 q h, clause1666 q h, clause1667 q h, clause1668 q h, clause1669 q h, clause1670 q h, clause1671 q h, clause1672 q h, clause1673 q h, clause1674 q h, clause1675 q h, clause1676 q h, clause1677 q h, clause1678 q h, clause1679 q h, clause1680 q h, clause1681 q h, clause1682 q h, clause1683 q h, clause1684 q h, clause1685 q h, clause1686 q h, clause1687 q h, clause1688 q h, clause1689 q h, clause1690 q h, clause1691 q h, clause1692 q h, clause1693 q h, clause1694 q h, clause1695 q h, clause1696 q h⟩

end
end Snake9.Regrowth.E112121
