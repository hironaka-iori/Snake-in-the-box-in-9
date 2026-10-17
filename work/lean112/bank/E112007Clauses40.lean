import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 70 = false ∨ valuation q 88 = false ∨ valuation q 106 = false := by
  rw [value52, value70, value88, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (266 : Vertex) (330 : Vertex) (394 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value53, value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (272 : Vertex) (273 : Vertex) (274 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value54, value56, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (273 : Vertex) (275 : Vertex) (401 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 70 = false ∨ valuation q 72 = false := by
  rw [value65, value66, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (322 : Vertex) (326 : Vertex) (330 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 77 = false := by
  rw [value65, value70, value73, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (322 : Vertex) (330 : Vertex) (338 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 70 = false ∨ valuation q 101 = false ∨ valuation q 106 = false := by
  rw [value65, value70, value101, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (322 : Vertex) (330 : Vertex) (450 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 84 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value81, value84, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (390 : Vertex) (394 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 88 = false ∨ valuation q 101 = false ∨ valuation q 106 = false := by
  rw [value81, value88, value101, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (394 : Vertex) (450 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 92 = false ∨ valuation q 102 = false ∨ valuation q 112 = false := by
  rw [value82, value92, value102, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (387 : Vertex) (403 : Vertex) (451 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value83, value84, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (388 : Vertex) (390 : Vertex) (396 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value86, value87, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (392 : Vertex) (393 : Vertex) (408 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value86, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (392 : Vertex) (394 : Vertex) (396 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value86, value88, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (392 : Vertex) (394 : Vertex) (408 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 95 = false := by
  rw [value91, value92, value93, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (401 : Vertex) (403 : Vertex) (405 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value91, value92, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (401 : Vertex) (403 : Vertex) (465 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 93 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value91, value93, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (401 : Vertex) (405 : Vertex) (409 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value96, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (408 : Vertex) (409 : Vertex) (410 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 102 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value101, value102, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (450 : Vertex) (451 : Vertex) (458 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value113, value114, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (468 : Vertex) (470 : Vertex) (476 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E007.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h⟩

end
end Snake9.Regrowth.E112007
