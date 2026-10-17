import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) + (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (l₂ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1724 q) 16 5 (meaning1574 q) (meaning1707 q) (meaning1744 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1707 = false ∨ valuation q 1744 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1744 = true := by
  have hs : count1724 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) + (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (l₂ := [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (countLit q [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]) (count1724 q) 17 4 (meaning1575 q) (meaning1706 q) (meaning1744 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1706 = false ∨ valuation q 1744 = true := counterClause1474 (baseVal q)

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1744 = false := by
  rw [value1744]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1724 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 10 = false := by
  rw [value1, value4, value7, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (34 : Vertex) (38 : Vertex) (42 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 10 = false := by
  rw [value2, value4, value9, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (36 : Vertex) (38 : Vertex) (44 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 8 = false := by
  rw [value5, value6, value7, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (40 : Vertex) (41 : Vertex) (42 : Vertex) (43 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value5, value6, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (40 : Vertex) (41 : Vertex) (56 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 16 = false ∨ valuation q 47 = false ∨ valuation q 55 = false := by
  rw [value5, value16, value47, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (40 : Vertex) (56 : Vertex) (168 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value6, value8, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (41 : Vertex) (43 : Vertex) (105 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 37 = false := by
  rw [value6, value17, value25, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (41 : Vertex) (57 : Vertex) (105 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value11, value12, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (48 : Vertex) (49 : Vertex) (56 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 16 = false ∨ valuation q 30 = false ∨ valuation q 36 = false := by
  rw [value11, value16, value30, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (48 : Vertex) (56 : Vertex) (112 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 16 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value11, value16, value50, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (48 : Vertex) (56 : Vertex) (176 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 30 = false ∨ valuation q 50 = false ∨ valuation q 67 = false := by
  rw [value11, value30, value50, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (48 : Vertex) (112 : Vertex) (176 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 15 = false := by
  rw [value12, value13, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (49 : Vertex) (51 : Vertex) (53 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value18, value19, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (62 : Vertex) (63 : Vertex) (126 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value20, value21, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (96 : Vertex) (97 : Vertex) (98 : Vertex) (99 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value20, value22, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (96 : Vertex) (98 : Vertex) (112 : Vertex) (114 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value21, value23, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (97 : Vertex) (99 : Vertex) (105 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 29 = false := by
  rw [value23, value24, value26, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (99 : Vertex) (103 : Vertex) (107 : Vertex) (111 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 32 = false ∨ valuation q 35 = false := by
  rw [value23, value24, value32, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (99 : Vertex) (103 : Vertex) (115 : Vertex) (119 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 29 = false ∨ valuation q 35 = false ∨ valuation q 42 = false := by
  rw [value24, value29, value35, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (103 : Vertex) (111 : Vertex) (119 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 35 = false ∨ valuation q 96 = false ∨ valuation q 105 = false := by
  rw [value24, value35, value96, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (103 : Vertex) (119 : Vertex) (359 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value25, value26, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (105 : Vertex) (107 : Vertex) (109 : Vertex) (111 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value25, value26, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (105 : Vertex) (107 : Vertex) (361 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 37 = false ∨ valuation q 40 = false := by
  rw [value25, value28, value37, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (105 : Vertex) (109 : Vertex) (121 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 37 = false ∨ valuation q 63 = false ∨ valuation q 72 = false := by
  rw [value25, value37, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (105 : Vertex) (121 : Vertex) (233 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 37 = false ∨ valuation q 98 = false ∨ valuation q 107 = false := by
  rw [value25, value37, value98, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (105 : Vertex) (121 : Vertex) (361 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value27, value28, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (108 : Vertex) (109 : Vertex) (124 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 33 = false ∨ valuation q 34 = false := by
  rw [value30, value31, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (112 : Vertex) (114 : Vertex) (116 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 36 = false ∨ valuation q 38 = false := by
  rw [value30, value31, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (112 : Vertex) (114 : Vertex) (120 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 39 = false := by
  rw [value30, value33, value36, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (112 : Vertex) (116 : Vertex) (120 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E040.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112040
