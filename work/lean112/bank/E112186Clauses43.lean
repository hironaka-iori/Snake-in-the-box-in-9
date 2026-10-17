import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value83, value85, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (385 : Vertex) (387 : Vertex) (401 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 88 = false ∨ valuation q 95 = false ∨ valuation q 100 = false := by
  rw [value83, value88, value95, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (385 : Vertex) (393 : Vertex) (401 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value84, value85, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (387 : Vertex) (402 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value84, value85, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (387 : Vertex) (450 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 107 = false ∨ valuation q 110 = false := by
  rw [value85, value87, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (387 : Vertex) (391 : Vertex) (451 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 93 = false := by
  rw [value86, value87, value91, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (389 : Vertex) (391 : Vertex) (397 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value88, value91, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (393 : Vertex) (397 : Vertex) (409 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 100 = false ∨ valuation q 112 = false ∨ valuation q 120 = false := by
  rw [value88, value100, value112, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (393 : Vertex) (409 : Vertex) (457 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 101 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value89, value101, value113, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (394 : Vertex) (410 : Vertex) (458 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value90, value91, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (396 : Vertex) (397 : Vertex) (398 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value90, value91, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (396 : Vertex) (397 : Vertex) (412 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 92 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value90, value92, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (396 : Vertex) (398 : Vertex) (412 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 92 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value90, value92, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (396 : Vertex) (398 : Vertex) (460 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value94, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (400 : Vertex) (401 : Vertex) (402 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value99, value100, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (408 : Vertex) (409 : Vertex) (412 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 101 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value99, value101, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (408 : Vertex) (410 : Vertex) (412 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value105, value106, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (448 : Vertex) (450 : Vertex) (452 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value105, value108, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (448 : Vertex) (452 : Vertex) (464 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 109 = false ∨ valuation q 110 = false := by
  rw [value106, value107, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (450 : Vertex) (451 : Vertex) (454 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value108, value109, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (452 : Vertex) (454 : Vertex) (460 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value111, value113, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (456 : Vertex) (458 : Vertex) (460 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 119 = false ∨ valuation q 123 = false ∨ valuation q 124 = false := by
  rw [value118, value119, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (469 : Vertex) (471 : Vertex) (477 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 122 = false ∨ valuation q 123 = false ∨ valuation q 124 = false := by
  rw [value120, value122, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (473 : Vertex) (475 : Vertex) (477 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E186.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h⟩

end
end Snake9.Regrowth.E112186
