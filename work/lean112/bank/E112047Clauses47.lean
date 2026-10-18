import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value14, value15, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (128 : Vertex) (129 : Vertex) (144 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 18 = false ∨ valuation q 24 = false ∨ valuation q 28 = false := by
  rw [value14, value18, value24, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (128 : Vertex) (132 : Vertex) (144 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 29 = false := by
  rw [value16, value21, value26, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (138 : Vertex) (146 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 21 = false ∨ valuation q 80 = false ∨ valuation q 87 = false := by
  rw [value16, value21, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (138 : Vertex) (386 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 38 = false ∨ valuation q 86 = false ∨ valuation q 104 = false := by
  rw [value20, value38, value86, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (137 : Vertex) (201 : Vertex) (393 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 29 = false ∨ valuation q 87 = false ∨ valuation q 97 = false := by
  rw [value21, value29, value87, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (138 : Vertex) (154 : Vertex) (394 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 27 = false := by
  rw [value24, value25, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (144 : Vertex) (145 : Vertex) (146 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 27 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value25, value27, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (145 : Vertex) (147 : Vertex) (401 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value35, value36, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (198 : Vertex) (199 : Vertex) (214 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value45, value46, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (216 : Vertex) (217 : Vertex) (218 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value50, value51, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (259 : Vertex) (386 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 64 = false ∨ valuation q 69 = false := by
  rw [value50, value52, value64, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (266 : Vertex) (322 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 80 = false ∨ valuation q 87 = false := by
  rw [value50, value52, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (266 : Vertex) (386 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 81 = false ∨ valuation q 91 = false := by
  rw [value51, value55, value81, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (259 : Vertex) (275 : Vertex) (387 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 69 = false ∨ valuation q 87 = false ∨ valuation q 105 = false := by
  rw [value52, value69, value87, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (266 : Vertex) (330 : Vertex) (394 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value54, value55, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (273 : Vertex) (275 : Vertex) (401 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value62, value63, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (321 : Vertex) (328 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 69 = false := by
  rw [value62, value64, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (322 : Vertex) (328 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 71 = false := by
  rw [value64, value65, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (322 : Vertex) (326 : Vertex) (330 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 76 = false := by
  rw [value64, value69, value72, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (322 : Vertex) (330 : Vertex) (338 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 69 = false ∨ valuation q 100 = false ∨ valuation q 105 = false := by
  rw [value64, value69, value100, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (322 : Vertex) (330 : Vertex) (450 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 88 = false := by
  rw [value79, value82, value85, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (388 : Vertex) (392 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value80, value81, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (387 : Vertex) (390 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 87 = false ∨ valuation q 100 = false ∨ valuation q 105 = false := by
  rw [value80, value87, value100, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (394 : Vertex) (450 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 91 = false ∨ valuation q 101 = false ∨ valuation q 112 = false := by
  rw [value81, value91, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (387 : Vertex) (403 : Vertex) (451 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value82, value83, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (388 : Vertex) (390 : Vertex) (396 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value83, value84, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (390 : Vertex) (391 : Vertex) (406 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value85, value86, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (392 : Vertex) (393 : Vertex) (408 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value85, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (392 : Vertex) (394 : Vertex) (396 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value85, value87, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (392 : Vertex) (394 : Vertex) (408 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 94 = false := by
  rw [value90, value91, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (401 : Vertex) (403 : Vertex) (405 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value90, value91, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (401 : Vertex) (403 : Vertex) (409 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E047.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112047
