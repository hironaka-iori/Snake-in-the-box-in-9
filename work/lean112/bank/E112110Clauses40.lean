import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value76, value79, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (388 : Vertex) (392 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 80 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value77, value80, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (385 : Vertex) (389 : Vertex) (449 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 81 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value78, value81, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (390 : Vertex) (402 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value79, value81, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (388 : Vertex) (390 : Vertex) (396 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 91 = false ∨ valuation q 102 = false ∨ valuation q 113 = false := by
  rw [value82, value91, value102, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (392 : Vertex) (408 : Vertex) (456 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 93 = false ∨ valuation q 103 = false ∨ valuation q 115 = false := by
  rw [value84, value93, value103, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (395 : Vertex) (411 : Vertex) (459 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value85, value86, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (396 : Vertex) (398 : Vertex) (460 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value88, value90, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (405 : Vertex) (407 : Vertex) (413 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value92, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (409 : Vertex) (411 : Vertex) (413 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value96, value97, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (448 : Vertex) (449 : Vertex) (464 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value97, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (451 : Vertex) (453 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value97, value99, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (451 : Vertex) (465 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 101 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value99, value101, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (451 : Vertex) (455 : Vertex) (459 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 103 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value99, value103, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (451 : Vertex) (459 : Vertex) (467 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value104, value106, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (460 : Vertex) (462 : Vertex) (476 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value106, value107, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (462 : Vertex) (463 : Vertex) (478 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value108, value109, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (464 : Vertex) (465 : Vertex) (466 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value108, value112, value113, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (464 : Vertex) (468 : Vertex) (472 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value110, value111, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (466 : Vertex) (467 : Vertex) (474 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value113, value114, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (472 : Vertex) (474 : Vertex) (476 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E110.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h⟩

end
end Snake9.Regrowth.E112110
