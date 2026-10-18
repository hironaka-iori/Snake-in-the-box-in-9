import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 69 = false ∨ valuation q 73 = false := by
  rw [value10, value15, value69, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (263 : Vertex) (271 : Vertex) (391 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 69 = false ∨ valuation q 76 = false := by
  rw [value10, value19, value69, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (263 : Vertex) (279 : Vertex) (391 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 27 = false ∨ valuation q 69 = false ∨ valuation q 85 = false := by
  rw [value10, value27, value69, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (263 : Vertex) (295 : Vertex) (391 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 45 = false ∨ valuation q 69 = false ∨ valuation q 104 = false := by
  rw [value10, value45, value69, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (263 : Vertex) (327 : Vertex) (391 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 70 = false ∨ valuation q 72 = false := by
  rw [value11, value14, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (264 : Vertex) (268 : Vertex) (392 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value12, value13, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (265 : Vertex) (267 : Vertex) (297 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 20 = false ∨ valuation q 71 = false ∨ valuation q 77 = false := by
  rw [value12, value20, value71, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (265 : Vertex) (281 : Vertex) (393 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 23 = false ∨ valuation q 73 = false ∨ valuation q 81 = false := by
  rw [value15, value23, value73, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (271 : Vertex) (287 : Vertex) (399 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 32 = false ∨ valuation q 35 = false := by
  rw [value16, value18, value32, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (272 : Vertex) (276 : Vertex) (304 : Vertex) (308 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 35 = false ∨ valuation q 75 = false ∨ valuation q 94 = false := by
  rw [value18, value35, value75, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (276 : Vertex) (308 : Vertex) (404 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 76 = false ∨ valuation q 81 = false := by
  rw [value19, value23, value76, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (279 : Vertex) (287 : Vertex) (407 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 77 = false ∨ valuation q 80 = false := by
  rw [value20, value22, value77, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (281 : Vertex) (285 : Vertex) (409 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 38 = false ∨ valuation q 78 = false ∨ valuation q 98 = false := by
  rw [value21, value38, value78, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (282 : Vertex) (314 : Vertex) (410 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value22, value23, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (285 : Vertex) (287 : Vertex) (317 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value22, value23, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (285 : Vertex) (287 : Vertex) (413 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 39 = false ∨ valuation q 80 = false ∨ valuation q 100 = false := by
  rw [value22, value39, value80, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (285 : Vertex) (317 : Vertex) (413 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 86 = false ∨ valuation q 88 = false := by
  rw [value28, value29, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (297 : Vertex) (299 : Vertex) (425 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 40 = false ∨ valuation q 90 = false ∨ valuation q 101 = false := by
  rw [value31, value40, value90, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (302 : Vertex) (318 : Vertex) (430 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 91 = false ∨ valuation q 97 = false := by
  rw [value32, value37, value91, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (304 : Vertex) (312 : Vertex) (432 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value33, value34, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (305 : Vertex) (307 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value35, value36, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (308 : Vertex) (310 : Vertex) (436 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 40 = false ∨ valuation q 96 = false ∨ valuation q 101 = false := by
  rw [value36, value40, value96, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (310 : Vertex) (318 : Vertex) (438 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value37, value38, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (312 : Vertex) (314 : Vertex) (440 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value50, value51, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (344 : Vertex) (345 : Vertex) (376 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value57, value58, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (368 : Vertex) (370 : Vertex) (496 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 118 = false ∨ valuation q 121 = false := by
  rw [value58, value61, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (370 : Vertex) (378 : Vertex) (498 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value59, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (376 : Vertex) (377 : Vertex) (378 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value64, value65, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (385 : Vertex) (392 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 72 = false := by
  rw [value64, value67, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (388 : Vertex) (392 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value64, value67, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (388 : Vertex) (416 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 72 = false ∨ valuation q 75 = false ∨ valuation q 79 = false := by
  rw [value67, value72, value75, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (388 : Vertex) (396 : Vertex) (404 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 75 = false ∨ valuation q 84 = false ∨ valuation q 94 = false := by
  rw [value67, value75, value84, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (388 : Vertex) (404 : Vertex) (420 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E254.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112254
