import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value5, value7, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (8 : Vertex) (10 : Vertex) (40 : Vertex) (42 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 14 = false ∨ valuation q 60 = false ∨ valuation q 70 = false := by
  rw [value5, value14, value60, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (8 : Vertex) (24 : Vertex) (136 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 23 = false ∨ valuation q 60 = false ∨ valuation q 81 = false := by
  rw [value5, value23, value60, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (8 : Vertex) (40 : Vertex) (136 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 61 = false ∨ valuation q 63 = false := by
  rw [value6, value8, value61, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (9 : Vertex) (13 : Vertex) (137 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 64 = false ∨ valuation q 73 = false := by
  rw [value9, value17, value64, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (14 : Vertex) (30 : Vertex) (142 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 28 = false ∨ valuation q 30 = false := by
  rw [value10, value12, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (17 : Vertex) (21 : Vertex) (49 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 65 = false ∨ valuation q 69 = false := by
  rw [value11, value13, value65, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (18 : Vertex) (22 : Vertex) (146 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 29 = false ∨ valuation q 65 = false ∨ valuation q 88 = false := by
  rw [value11, value29, value65, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (18 : Vertex) (50 : Vertex) (146 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 30 = false ∨ valuation q 68 = false ∨ valuation q 90 = false := by
  rw [value12, value30, value68, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (21 : Vertex) (53 : Vertex) (149 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 71 = false ∨ valuation q 74 = false := by
  rw [value15, value18, value71, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (27 : Vertex) (31 : Vertex) (155 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 34 = false ∨ valuation q 35 = false := by
  rw [value16, value17, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (28 : Vertex) (30 : Vertex) (60 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 35 = false ∨ valuation q 73 = false ∨ valuation q 95 = false := by
  rw [value17, value35, value73, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (30 : Vertex) (62 : Vertex) (158 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 76 = false ∨ valuation q 78 = false := by
  rw [value19, value20, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (33 : Vertex) (35 : Vertex) (161 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 76 = false ∨ valuation q 87 = false := by
  rw [value19, value28, value76, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (33 : Vertex) (49 : Vertex) (161 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value23, value24, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (40 : Vertex) (42 : Vertex) (168 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value27, value28, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (48 : Vertex) (49 : Vertex) (176 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 86 = false ∨ valuation q 88 = false := by
  rw [value27, value29, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (48 : Vertex) (50 : Vertex) (176 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 30 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value28, value30, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (49 : Vertex) (53 : Vertex) (177 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 32 = false ∨ valuation q 87 = false ∨ valuation q 92 = false := by
  rw [value28, value32, value87, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (49 : Vertex) (57 : Vertex) (177 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value30, value31, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (53 : Vertex) (55 : Vertex) (181 : Vertex) (183 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value44, value45, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (105 : Vertex) (107 : Vertex) (233 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value54, value55, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (128 : Vertex) (129 : Vertex) (136 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value54, value55, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (128 : Vertex) (129 : Vertex) (160 : Vertex) (161 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 76 = false ∨ valuation q 78 = false := by
  rw [value55, value56, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (131 : Vertex) (161 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 63 = false := by
  rw [value55, value58, value61, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (133 : Vertex) (137 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 71 = false := by
  rw [value56, value62, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (131 : Vertex) (139 : Vertex) (147 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 67 = false ∨ valuation q 79 = false ∨ valuation q 89 = false := by
  rw [value57, value67, value79, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (148 : Vertex) (164 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 63 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value58, value63, value68, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (133 : Vertex) (141 : Vertex) (149 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 64 = false ∨ valuation q 69 = false ∨ valuation q 73 = false := by
  rw [value59, value64, value69, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (134 : Vertex) (142 : Vertex) (150 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value67, value68, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (148 : Vertex) (149 : Vertex) (180 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 103 = false ∨ valuation q 104 = false := by
  rw [value75, value76, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (224 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 84 = false := by
  rw [value75, value79, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (164 : Vertex) (168 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E259.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112259
