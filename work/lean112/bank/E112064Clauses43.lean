import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value4, value5, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (72 : Vertex) (73 : Vertex) (88 : Vertex) (89 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value5, value7, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (73 : Vertex) (75 : Vertex) (329 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 14 = false ∨ valuation q 69 = false ∨ valuation q 81 = false := by
  rw [value5, value14, value69, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (73 : Vertex) (89 : Vertex) (329 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 37 = false ∨ valuation q 42 = false := by
  rw [value9, value13, value37, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (80 : Vertex) (88 : Vertex) (208 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 74 = false ∨ valuation q 80 = false := by
  rw [value9, value13, value74, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (80 : Vertex) (88 : Vertex) (336 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 37 = false ∨ valuation q 74 = false ∨ valuation q 109 = false := by
  rw [value9, value37, value74, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (80 : Vertex) (208 : Vertex) (336 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 76 = false ∨ valuation q 79 = false := by
  rw [value10, value12, value76, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (83 : Vertex) (87 : Vertex) (339 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 42 = false ∨ valuation q 80 = false ∨ valuation q 114 = false := by
  rw [value13, value42, value80, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (88 : Vertex) (216 : Vertex) (344 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 81 = false ∨ valuation q 84 = false := by
  rw [value14, value15, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (89 : Vertex) (93 : Vertex) (345 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 45 = false ∨ valuation q 85 = false ∨ valuation q 116 = false := by
  rw [value16, value45, value85, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (94 : Vertex) (222 : Vertex) (350 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 33 = false := by
  rw [value29, value31, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (193 : Vertex) (195 : Vertex) (197 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value37, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (208 : Vertex) (210 : Vertex) (212 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value37, value39, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (208 : Vertex) (210 : Vertex) (216 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 42 = false ∨ valuation q 109 = false ∨ valuation q 114 = false := by
  rw [value37, value42, value109, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (208 : Vertex) (216 : Vertex) (464 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value39, value41, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (210 : Vertex) (214 : Vertex) (218 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 44 = false ∨ valuation q 45 = false := by
  rw [value40, value41, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (212 : Vertex) (214 : Vertex) (220 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value45, value46, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (222 : Vertex) (223 : Vertex) (478 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value47, value50, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (262 : Vertex) (266 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value51, value53, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (265 : Vertex) (267 : Vertex) (329 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 61 = false ∨ valuation q 69 = false ∨ valuation q 81 = false := by
  rw [value51, value61, value69, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (265 : Vertex) (281 : Vertex) (329 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value55, value56, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (272 : Vertex) (273 : Vertex) (280 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value56, value57, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (273 : Vertex) (275 : Vertex) (277 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value62, value63, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (286 : Vertex) (287 : Vertex) (350 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value64, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (321 : Vertex) (322 : Vertex) (323 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value65, value67, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (321 : Vertex) (323 : Vertex) (329 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value67, value68, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (323 : Vertex) (327 : Vertex) (331 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 76 = false ∨ valuation q 79 = false := by
  rw [value67, value68, value76, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (323 : Vertex) (327 : Vertex) (339 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 73 = false ∨ valuation q 79 = false ∨ valuation q 86 = false := by
  rw [value68, value73, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (327 : Vertex) (335 : Vertex) (343 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value69, value70, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (329 : Vertex) (331 : Vertex) (457 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 81 = false ∨ valuation q 105 = false ∨ valuation q 115 = false := by
  rw [value69, value81, value105, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (329 : Vertex) (345 : Vertex) (457 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value71, value72, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (332 : Vertex) (333 : Vertex) (348 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 80 = false ∨ valuation q 82 = false := by
  rw [value74, value75, value80, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (336 : Vertex) (338 : Vertex) (344 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E064.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112064
