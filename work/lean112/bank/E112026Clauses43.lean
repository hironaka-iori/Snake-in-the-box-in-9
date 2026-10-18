import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value57, value58, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (304 : Vertex) (305 : Vertex) (306 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value58, value60, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (305 : Vertex) (307 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value61, value62, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (308 : Vertex) (310 : Vertex) (316 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value68, value69, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (356 : Vertex) (357 : Vertex) (372 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 84 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value81, value84, value88, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (420 : Vertex) (424 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 88 = false ∨ valuation q 104 = false ∨ valuation q 108 = false := by
  rw [value81, value88, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (424 : Vertex) (480 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 94 = false ∨ valuation q 97 = false := by
  rw [value82, value85, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (417 : Vertex) (421 : Vertex) (433 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 92 = false := by
  rw [value83, value86, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (418 : Vertex) (422 : Vertex) (426 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value84, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value84, value85, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (421 : Vertex) (436 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value84, value86, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (422 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value85, value87, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (421 : Vertex) (423 : Vertex) (437 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value86, value87, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (422 : Vertex) (423 : Vertex) (486 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 103 = false := by
  rw [value87, value93, value98, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (423 : Vertex) (431 : Vertex) (439 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value88, value89, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (426 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value88, value89, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (426 : Vertex) (440 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value89, value90, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (426 : Vertex) (427 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value90, value93, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (427 : Vertex) (431 : Vertex) (443 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value94, value95, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (433 : Vertex) (435 : Vertex) (437 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value94, value95, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (433 : Vertex) (435 : Vertex) (497 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 98 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value95, value98, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (435 : Vertex) (439 : Vertex) (443 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value99, value100, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (440 : Vertex) (441 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value104, value105, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (481 : Vertex) (488 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value109, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (489 : Vertex) (491 : Vertex) (493 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 117 = false ∨ valuation q 119 = false ∨ valuation q 121 = false := by
  rw [value116, value117, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (500 : Vertex) (502 : Vertex) (508 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E026.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h⟩

end
end Snake9.Regrowth.E112026
