import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) + (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (l₂ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1782)) (literal (valuationOf q) (1816)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1794 q) 11 12 (meaning1630 q) (meaning1782 q) (meaning1816 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1782 = false ∨ valuation q 1816 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) + (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (l₂ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1781)) (literal (valuationOf q) (1816)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1794 q) 12 11 (meaning1631 q) (meaning1781 q) (meaning1816 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1781 = false ∨ valuation q 1816 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1780 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) + (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (l₂ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1780)) (literal (valuationOf q) (1816)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1794 q) 13 10 (meaning1632 q) (meaning1780 q) (meaning1816 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1780 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1780 = false ∨ valuation q 1816 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1779 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) + (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (l₂ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1633)) (literal (valuationOf q) (1779)) (literal (valuationOf q) (1816)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1794 q) 14 9 (meaning1633 q) (meaning1779 q) (meaning1816 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1779 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1779 = false ∨ valuation q 1816 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1778 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) + (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (l₂ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1778)) (literal (valuationOf q) (1816)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1794 q) 15 8 (meaning1634 q) (meaning1778 q) (meaning1816 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1778 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1778 = false ∨ valuation q 1816 = true := counterClause1349 (baseVal q)

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1816 = false := by
  rw [value1816]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1794 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 34 = false ∨ valuation q 69 = false ∨ valuation q 111 = false := by
  rw [value2, value34, value69, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (72 : Vertex) (200 : Vertex) (328 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 17 = false ∨ valuation q 18 = false := by
  rw [value12, value13, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (131 : Vertex) (138 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value12, value13, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (131 : Vertex) (386 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value14, value15, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (133 : Vertex) (148 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 27 = false ∨ valuation q 88 = false ∨ valuation q 100 = false := by
  rw [value16, value27, value88, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (137 : Vertex) (153 : Vertex) (393 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value19, value20, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (140 : Vertex) (142 : Vertex) (396 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 94 = false ∨ valuation q 99 = false := by
  rw [value21, value26, value94, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (144 : Vertex) (152 : Vertex) (400 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value22, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (148 : Vertex) (149 : Vertex) (150 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value32, value33, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (197 : Vertex) (199 : Vertex) (205 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value35, value36, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (201 : Vertex) (203 : Vertex) (205 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 46 = false := by
  rw [value40, value42, value43, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (210 : Vertex) (214 : Vertex) (218 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value47, value48, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (259 : Vertex) (266 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value47, value48, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (259 : Vertex) (322 : Vertex) (323 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value47, value48, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (259 : Vertex) (386 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value48, value53, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (259 : Vertex) (267 : Vertex) (323 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 67 = false ∨ valuation q 85 = false ∨ valuation q 107 = false := by
  rw [value48, value67, value85, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (259 : Vertex) (323 : Vertex) (387 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value51, value53, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (265 : Vertex) (267 : Vertex) (281 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 61 = false ∨ valuation q 88 = false ∨ valuation q 100 = false := by
  rw [value51, value61, value88, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (265 : Vertex) (281 : Vertex) (393 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value54, value55, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (268 : Vertex) (270 : Vertex) (396 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 60 = false ∨ valuation q 94 = false ∨ valuation q 99 = false := by
  rw [value56, value60, value94, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (272 : Vertex) (280 : Vertex) (400 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value66, value67, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (322 : Vertex) (323 : Vertex) (338 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value66, value67, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (322 : Vertex) (323 : Vertex) (450 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 79 = false ∨ valuation q 81 = false := by
  rw [value71, value72, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (333 : Vertex) (335 : Vertex) (349 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value78, value79, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (348 : Vertex) (349 : Vertex) (350 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value82, value83, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (385 : Vertex) (386 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value83, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (385 : Vertex) (387 : Vertex) (389 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E186.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112186
