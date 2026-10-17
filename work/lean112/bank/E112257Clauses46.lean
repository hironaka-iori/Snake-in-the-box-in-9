import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1672 = true := by
  have hs : count1655 q = (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27, -29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) + (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84, -86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27, -29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (l₂ := [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84, -86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1672)) (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27, -29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84, -86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) (count1655 q) 7 11 (meaning1512 q) (meaning1647 q) (meaning1672 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1647 = false ∨ valuation q 1672 = true := counterClause1473 (baseVal q)

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false := by
  rw [value1672]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1655 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 36 = false ∨ valuation q 46 = false := by
  rw [value1, value10, value36, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (16 : Vertex) (128 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 37 = false ∨ valuation q 40 = false := by
  rw [value2, value5, value37, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (3 : Vertex) (7 : Vertex) (131 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 21 = false ∨ valuation q 22 = false := by
  rw [value3, value4, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (4 : Vertex) (6 : Vertex) (36 : Vertex) (38 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 39 = false ∨ valuation q 50 = false := by
  rw [value4, value14, value39, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (6 : Vertex) (22 : Vertex) (134 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 22 = false ∨ valuation q 39 = false ∨ valuation q 60 = false := by
  rw [value4, value22, value39, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (6 : Vertex) (38 : Vertex) (134 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value6, value8, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (9 : Vertex) (13 : Vertex) (41 : Vertex) (45 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 41 = false ∨ valuation q 45 = false := by
  rw [value7, value9, value41, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (10 : Vertex) (14 : Vertex) (138 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 25 = false ∨ valuation q 41 = false ∨ valuation q 63 = false := by
  rw [value7, value25, value41, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (10 : Vertex) (42 : Vertex) (138 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 26 = false ∨ valuation q 44 = false ∨ valuation q 65 = false := by
  rw [value8, value26, value44, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (13 : Vertex) (45 : Vertex) (141 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value10, value12, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (16 : Vertex) (18 : Vertex) (48 : Vertex) (50 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 46 = false ∨ valuation q 51 = false := by
  rw [value10, value15, value46, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (16 : Vertex) (24 : Vertex) (144 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 28 = false ∨ valuation q 46 = false ∨ valuation q 67 = false := by
  rw [value10, value28, value46, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (16 : Vertex) (48 : Vertex) (144 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 47 = false ∨ valuation q 49 = false := by
  rw [value11, value13, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (17 : Vertex) (21 : Vertex) (145 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value15, value17, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (24 : Vertex) (28 : Vertex) (152 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 33 = false ∨ valuation q 53 = false ∨ valuation q 75 = false := by
  rw [value16, value33, value53, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (27 : Vertex) (59 : Vertex) (155 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 34 = false ∨ valuation q 54 = false ∨ valuation q 76 = false := by
  rw [value17, value34, value54, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (28 : Vertex) (60 : Vertex) (156 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 24 = false ∨ valuation q 57 = false ∨ valuation q 62 = false := by
  rw [value19, value24, value57, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (33 : Vertex) (41 : Vertex) (161 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value23, value24, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (40 : Vertex) (41 : Vertex) (168 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 61 = false ∨ valuation q 63 = false := by
  rw [value23, value25, value61, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (40 : Vertex) (42 : Vertex) (168 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 32 = false ∨ valuation q 62 = false ∨ valuation q 73 = false := by
  rw [value24, value32, value62, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (41 : Vertex) (57 : Vertex) (169 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value26, value27, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (45 : Vertex) (47 : Vertex) (173 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value28, value29, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (48 : Vertex) (50 : Vertex) (176 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value32, value33, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (57 : Vertex) (59 : Vertex) (185 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 42 = false ∨ valuation q 48 = false ∨ valuation q 53 = false := by
  rw [value37, value42, value48, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (131 : Vertex) (139 : Vertex) (147 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 44 = false ∨ valuation q 59 = false ∨ valuation q 65 = false := by
  rw [value38, value44, value59, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (133 : Vertex) (141 : Vertex) (165 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 45 = false ∨ valuation q 50 = false ∨ valuation q 56 = false := by
  rw [value39, value45, value50, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (134 : Vertex) (142 : Vertex) (150 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 54 = false ∨ valuation q 64 = false ∨ valuation q 76 = false := by
  rw [value43, value54, value64, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (140 : Vertex) (156 : Vertex) (172 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value46, value47, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (144 : Vertex) (145 : Vertex) (152 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 51 = false ∨ valuation q 67 = false ∨ valuation q 72 = false := by
  rw [value46, value51, value67, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (144 : Vertex) (152 : Vertex) (176 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value47, value48, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (145 : Vertex) (147 : Vertex) (153 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E257.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112257
