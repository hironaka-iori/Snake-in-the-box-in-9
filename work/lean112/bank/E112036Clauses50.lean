import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec50 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1601 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 58 = false ∨ valuation q 97 = false ∨ valuation q 117 = false := by
  rw [value38, value58, value97, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (171 : Vertex) (235 : Vertex) (427 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1602 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 48 = false ∨ valuation q 50 = false := by
  rw [value39, value40, value48, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (173 : Vertex) (175 : Vertex) (189 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1603 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value41, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1604 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 44 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value42, value44, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (177 : Vertex) (179 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1605 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value47, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (188 : Vertex) (189 : Vertex) (190 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1606 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value51, value55, value57, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (226 : Vertex) (230 : Vertex) (234 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1607 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value53, value54, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (229 : Vertex) (244 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1608 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value53, value55, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (230 : Vertex) (236 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1609 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 65 = false ∨ valuation q 67 = false := by
  rw [value56, value58, value65, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (233 : Vertex) (235 : Vertex) (249 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1610 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value56, value58, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (233 : Vertex) (235 : Vertex) (489 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1611 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value57, value58, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (234 : Vertex) (235 : Vertex) (250 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1612 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value64, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (248 : Vertex) (249 : Vertex) (250 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1613 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 74 = false := by
  rw [value69, value70, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1614 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value69, value70, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (289 : Vertex) (416 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1615 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 73 = false ∨ valuation q 88 = false ∨ valuation q 95 = false := by
  rw [value69, value73, value88, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (296 : Vertex) (416 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1616 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 78 = false ∨ valuation q 89 = false ∨ valuation q 101 = false := by
  rw [value70, value78, value89, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (289 : Vertex) (305 : Vertex) (417 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1617 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 77 = false ∨ valuation q 94 = false ∨ valuation q 100 = false := by
  rw [value72, value77, value94, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (295 : Vertex) (303 : Vertex) (423 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1618 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value74, value75, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (297 : Vertex) (299 : Vertex) (301 : Vertex) (303 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1619 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value75, value77, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (299 : Vertex) (303 : Vertex) (427 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1620 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 80 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value78, value80, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (305 : Vertex) (307 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1621 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value88, value89, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (417 : Vertex) (420 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1622 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value88, value90, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (418 : Vertex) (424 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1623 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 95 = false ∨ valuation q 98 = false := by
  rw [value88, value91, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (420 : Vertex) (424 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1624 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 95 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value88, value95, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (424 : Vertex) (480 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1625 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 96 = false ∨ valuation q 99 = false := by
  rw [value90, value93, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (418 : Vertex) (422 : Vertex) (426 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1626 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value91, value92, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1627 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value91, value93, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (422 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1628 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 94 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value92, value94, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (421 : Vertex) (423 : Vertex) (437 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1629 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value93, value94, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (422 : Vertex) (423 : Vertex) (486 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1630 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 100 = false ∨ valuation q 105 = false ∨ valuation q 110 = false := by
  rw [value94, value100, value105, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (423 : Vertex) (431 : Vertex) (439 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1631 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 100 = false ∨ valuation q 114 = false ∨ valuation q 119 = false := by
  rw [value94, value100, value114, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (423 : Vertex) (431 : Vertex) (487 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1632 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value95, value96, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (426 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block50 (q : Snake 81) (h : Conditions q) : B112E036.Block50 (valuation q) :=
  ⟨clause1601 q h, clause1602 q h, clause1603 q h, clause1604 q h, clause1605 q h, clause1606 q h, clause1607 q h, clause1608 q h, clause1609 q h, clause1610 q h, clause1611 q h, clause1612 q h, clause1613 q h, clause1614 q h, clause1615 q h, clause1616 q h, clause1617 q h, clause1618 q h, clause1619 q h, clause1620 q h, clause1621 q h, clause1622 q h, clause1623 q h, clause1624 q h, clause1625 q h, clause1626 q h, clause1627 q h, clause1628 q h, clause1629 q h, clause1630 q h, clause1631 q h, clause1632 q h⟩

end
end Snake9.Regrowth.E112036
