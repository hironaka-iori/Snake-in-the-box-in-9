import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1708 = true := by
  have hs : count1692 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) + (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (l₂ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1708)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1692 q) 11 6 (meaning1555 q) (meaning1680 q) (meaning1708 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1680 = false ∨ valuation q 1708 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1708 = true := by
  have hs : count1692 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) + (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (l₂ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1708)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1692 q) 12 5 (meaning1556 q) (meaning1679 q) (meaning1708 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1679 = false ∨ valuation q 1708 = true := counterClause1410 (baseVal q)

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false := by
  rw [value1708]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1692 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 8 = false := by
  rw [value3, value4, value6, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (2 : Vertex) (6 : Vertex) (18 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 51 = false ∨ valuation q 55 = false := by
  rw [value3, value4, value51, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (2 : Vertex) (6 : Vertex) (258 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 11 = false ∨ valuation q 19 = false ∨ valuation q 37 = false := by
  rw [value4, value11, value19, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (6 : Vertex) (70 : Vertex) (134 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value15, value18, value21, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (128 : Vertex) (132 : Vertex) (136 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 20 = false := by
  rw [value16, value17, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (131 : Vertex) (134 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value16, value17, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (131 : Vertex) (386 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 83 = false ∨ valuation q 85 = false := by
  rw [value17, value20, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (131 : Vertex) (135 : Vertex) (387 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value18, value19, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (134 : Vertex) (140 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value19, value20, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (134 : Vertex) (135 : Vertex) (198 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value21, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (136 : Vertex) (138 : Vertex) (140 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 31 = false ∨ valuation q 87 = false ∨ valuation q 97 = false := by
  rw [value23, value31, value87, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (138 : Vertex) (154 : Vertex) (394 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value24, value25, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (140 : Vertex) (142 : Vertex) (396 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value36, value38, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (197 : Vertex) (199 : Vertex) (205 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value51, value52, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (259 : Vertex) (386 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 58 = false := by
  rw [value51, value55, value56, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (262 : Vertex) (266 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 82 = false ∨ valuation q 87 = false := by
  rw [value51, value56, value82, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (266 : Vertex) (386 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 58 = false := by
  rw [value53, value55, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (262 : Vertex) (268 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 65 = false ∨ valuation q 84 = false ∨ valuation q 104 = false := by
  rw [value54, value65, value84, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (325 : Vertex) (389 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value56, value58, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (266 : Vertex) (270 : Vertex) (394 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value57, value58, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (268 : Vertex) (270 : Vertex) (396 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value65, value67, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (325 : Vertex) (327 : Vertex) (333 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value80, value81, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (385 : Vertex) (400 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value81, value83, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (385 : Vertex) (387 : Vertex) (389 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 93 = false ∨ valuation q 95 = false := by
  rw [value81, value83, value93, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (385 : Vertex) (387 : Vertex) (401 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value81, value84, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (385 : Vertex) (389 : Vertex) (393 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value82, value83, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (387 : Vertex) (450 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 87 = false ∨ valuation q 94 = false ∨ valuation q 97 = false := by
  rw [value82, value87, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (394 : Vertex) (402 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 87 = false ∨ valuation q 101 = false ∨ valuation q 106 = false := by
  rw [value82, value87, value101, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (394 : Vertex) (450 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value88, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (396 : Vertex) (397 : Vertex) (398 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E027.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112027
