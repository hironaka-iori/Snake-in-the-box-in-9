import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 90 = false ∨ valuation q 93 = false := by
  rw [value55, value57, value90, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (299 : Vertex) (303 : Vertex) (427 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 71 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value55, value71, value90, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (299 : Vertex) (363 : Vertex) (427 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value58, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (304 : Vertex) (305 : Vertex) (306 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value66, value67, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (354 : Vertex) (355 : Vertex) (362 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 84 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value81, value84, value88, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (420 : Vertex) (424 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value84, value86, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (422 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value85, value87, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (421 : Vertex) (423 : Vertex) (437 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value86, value87, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (422 : Vertex) (423 : Vertex) (486 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 103 = false := by
  rw [value87, value93, value98, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (423 : Vertex) (431 : Vertex) (439 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value88, value89, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (426 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value94, value95, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (433 : Vertex) (435 : Vertex) (437 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value94, value95, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (433 : Vertex) (435 : Vertex) (497 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 98 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value95, value98, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (435 : Vertex) (439 : Vertex) (443 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value99, value100, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (440 : Vertex) (441 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value104, value105, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (481 : Vertex) (488 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value109, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (489 : Vertex) (491 : Vertex) (493 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 117 = false ∨ valuation q 119 = false ∨ valuation q 121 = false := by
  rw [value116, value117, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (500 : Vertex) (502 : Vertex) (508 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E024.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h⟩

end
end Snake9.Regrowth.E112024
