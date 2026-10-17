import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 61 = false ∨ valuation q 78 = false ∨ valuation q 115 = false := by
  rw [value26, value61, value78, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (114 : Vertex) (242 : Vertex) (370 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1570 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value33, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1571 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value33, value34, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1572 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 41 = false := by
  rw [value36, value37, value38, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (163 : Vertex) (167 : Vertex) (171 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1573 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value42, value43, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (177 : Vertex) (184 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1574 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 49 = false := by
  rw [value42, value44, value46, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (180 : Vertex) (184 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1575 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 47 = false ∨ valuation q 60 = false ∨ valuation q 67 = false := by
  rw [value43, value47, value60, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (177 : Vertex) (185 : Vertex) (241 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1576 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value44, value45, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (180 : Vertex) (182 : Vertex) (188 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1577 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value46, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (184 : Vertex) (186 : Vertex) (188 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1578 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 60 = false ∨ valuation q 63 = false := by
  rw [value51, value53, value60, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (225 : Vertex) (229 : Vertex) (241 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1579 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value52, value54, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (230 : Vertex) (236 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1580 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value55, value56, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (232 : Vertex) (234 : Vertex) (236 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1581 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 66 = false ∨ valuation q 107 = false ∨ valuation q 119 = false := by
  rw [value55, value66, value107, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (232 : Vertex) (248 : Vertex) (488 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1582 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 68 = false ∨ valuation q 109 = false ∨ valuation q 120 = false := by
  rw [value57, value68, value109, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (235 : Vertex) (251 : Vertex) (491 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1583 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 63 = false ∨ valuation q 67 = false ∨ valuation q 69 = false := by
  rw [value60, value63, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (241 : Vertex) (245 : Vertex) (249 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1584 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value61, value62, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (242 : Vertex) (243 : Vertex) (246 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1585 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value61, value62, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (242 : Vertex) (243 : Vertex) (498 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1586 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value61, value64, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (242 : Vertex) (246 : Vertex) (498 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1587 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 70 = false := by
  rw [value62, value65, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (243 : Vertex) (247 : Vertex) (251 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1588 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value63, value65, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (245 : Vertex) (247 : Vertex) (253 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1589 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value67, value68, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (249 : Vertex) (251 : Vertex) (253 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1590 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value69, value70, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (253 : Vertex) (255 : Vertex) (509 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1591 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value78, value79, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (370 : Vertex) (371 : Vertex) (378 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1592 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value78, value79, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (370 : Vertex) (371 : Vertex) (498 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1593 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 120 = false ∨ valuation q 124 = false := by
  rw [value83, value85, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (379 : Vertex) (383 : Vertex) (507 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1594 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value94, value95, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (434 : Vertex) (435 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1595 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value94, value95, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (434 : Vertex) (435 : Vertex) (498 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1596 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value100, value101, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (445 : Vertex) (447 : Vertex) (509 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1597 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value102, value103, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (481 : Vertex) (482 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1598 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value102, value103, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (481 : Vertex) (496 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1599 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 104 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value102, value104, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (482 : Vertex) (496 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1600 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 107 = false ∨ valuation q 113 = false ∨ valuation q 119 = false := by
  rw [value102, value107, value113, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (488 : Vertex) (496 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E020.Block49 (valuation q) :=
  ⟨clause1569 q h, clause1570 q h, clause1571 q h, clause1572 q h, clause1573 q h, clause1574 q h, clause1575 q h, clause1576 q h, clause1577 q h, clause1578 q h, clause1579 q h, clause1580 q h, clause1581 q h, clause1582 q h, clause1583 q h, clause1584 q h, clause1585 q h, clause1586 q h, clause1587 q h, clause1588 q h, clause1589 q h, clause1590 q h, clause1591 q h, clause1592 q h, clause1593 q h, clause1594 q h, clause1595 q h, clause1596 q h, clause1597 q h, clause1598 q h, clause1599 q h, clause1600 q h⟩

end
end Snake9.Regrowth.E112020
