import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 34 = false ∨ valuation q 36 = false := by
  rw [value29, value30, value34, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (131 : Vertex) (137 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 50 = false ∨ valuation q 52 = false := by
  rw [value29, value30, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (131 : Vertex) (193 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 39 = false := by
  rw [value30, value33, value36, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (131 : Vertex) (135 : Vertex) (139 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value30, value33, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (131 : Vertex) (135 : Vertex) (195 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value34, value37, value46, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (137 : Vertex) (141 : Vertex) (153 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value35, value36, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (138 : Vertex) (139 : Vertex) (142 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 58 = false ∨ valuation q 60 = false := by
  rw [value37, value39, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (141 : Vertex) (143 : Vertex) (205 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 48 = false ∨ valuation q 58 = false ∨ valuation q 69 = false := by
  rw [value37, value48, value58, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (141 : Vertex) (157 : Vertex) (205 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value40, value41, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (144 : Vertex) (146 : Vertex) (148 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 47 = false := by
  rw [value40, value41, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (144 : Vertex) (146 : Vertex) (152 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 61 = false ∨ valuation q 64 = false := by
  rw [value40, value42, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (144 : Vertex) (148 : Vertex) (208 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value49, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (193 : Vertex) (194 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value49, value50, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (193 : Vertex) (208 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value49, value51, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (194 : Vertex) (200 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 53 = false ∨ valuation q 61 = false ∨ valuation q 64 = false := by
  rw [value49, value53, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (196 : Vertex) (208 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value50, value52, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (193 : Vertex) (195 : Vertex) (209 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 63 = false ∨ valuation q 66 = false := by
  rw [value52, value54, value63, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (195 : Vertex) (199 : Vertex) (211 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 60 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value54, value60, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (199 : Vertex) (207 : Vertex) (455 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value57, value58, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (205 : Vertex) (206 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value57, value58, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (205 : Vertex) (220 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 59 = false ∨ valuation q 68 = false ∨ valuation q 70 = false := by
  rw [value57, value59, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (206 : Vertex) (220 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 69 = false ∨ valuation q 71 = false := by
  rw [value58, value60, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (205 : Vertex) (207 : Vertex) (221 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value59, value60, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (206 : Vertex) (207 : Vertex) (462 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 71 = false := by
  rw [value63, value66, value67, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (211 : Vertex) (215 : Vertex) (219 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value64, value65, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (212 : Vertex) (213 : Vertex) (220 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 69 = false ∨ valuation q 71 = false := by
  rw [value65, value66, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (213 : Vertex) (215 : Vertex) (221 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value65, value69, value112, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (213 : Vertex) (221 : Vertex) (469 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value68, value69, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (220 : Vertex) (221 : Vertex) (222 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value85, value86, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (386 : Vertex) (392 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value87, value88, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (388 : Vertex) (389 : Vertex) (396 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value95, value96, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (403 : Vertex) (407 : Vertex) (411 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value104, value105, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (454 : Vertex) (455 : Vertex) (462 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E158.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112158
