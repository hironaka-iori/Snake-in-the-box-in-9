import E112144Semantics
import B112E144Inputs
namespace Snake9.Regrowth.E112144
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) + (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (l₂ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1490)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1478 q) 4 9 (meaning1353 q) (meaning1473 q) (meaning1490 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1473 = false ∨ valuation q 1490 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) + (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (l₂ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1490)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1478 q) 5 8 (meaning1354 q) (meaning1472 q) (meaning1490 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1472 = false ∨ valuation q 1490 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) + (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (l₂ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1490)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1478 q) 6 7 (meaning1355 q) (meaning1471 q) (meaning1490 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1471 = false ∨ valuation q 1490 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) + (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (l₂ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1356)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1490)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1478 q) 7 6 (meaning1356 q) (meaning1470 q) (meaning1490 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1470 = false ∨ valuation q 1490 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) + (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (l₂ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1490)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26, -28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78, -82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1478 q) 8 5 (meaning1357 q) (meaning1469 q) (meaning1490 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1469 = false ∨ valuation q 1490 = true := counterClause357 (baseVal q)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false := by
  rw [value1490]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1478 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 7 = false := by
  rw [value2, value3, value6, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (13 : Vertex) (15 : Vertex) (29 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 12 = false ∨ valuation q 13 = false := by
  rw [value8, value9, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (66 : Vertex) (67 : Vertex) (74 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 17 = false ∨ valuation q 18 = false := by
  rw [value10, value11, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (68 : Vertex) (69 : Vertex) (84 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value20, value21, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (88 : Vertex) (89 : Vertex) (90 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E144.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h⟩

end
end Snake9.Regrowth.E112144
