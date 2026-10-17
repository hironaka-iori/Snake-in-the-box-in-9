import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1546 = true := by
  have hs : count1532 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) + (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (l₂ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1546)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1532 q) 7 8 (meaning1400 q) (meaning1524 q) (meaning1546 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1524 = false ∨ valuation q 1546 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1546 = true := by
  have hs : count1532 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) + (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (l₂ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1546)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1532 q) 8 7 (meaning1401 q) (meaning1523 q) (meaning1546 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1523 = false ∨ valuation q 1546 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1546 = true := by
  have hs : count1532 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) + (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (l₂ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1546)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1532 q) 9 6 (meaning1402 q) (meaning1522 q) (meaning1546 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1522 = false ∨ valuation q 1546 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1546 = true := by
  have hs : count1532 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) + (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (l₂ := [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1546)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (countLit q [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]) (count1532 q) 10 5 (meaning1403 q) (meaning1521 q) (meaning1546 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1521 = false ∨ valuation q 1546 = true := counterClause740 (baseVal q)

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false := by
  rw [value1546]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1532 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value11, value13, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (131 : Vertex) (137 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value12, value13, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (131 : Vertex) (386 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value18, value19, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (140 : Vertex) (141 : Vertex) (396 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value21, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (144 : Vertex) (146 : Vertex) (148 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 27 = false := by
  rw [value24, value25, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (148 : Vertex) (150 : Vertex) (156 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value44, value45, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (259 : Vertex) (261 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value44, value45, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (259 : Vertex) (265 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 51 = false := by
  rw [value44, value46, value48, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (261 : Vertex) (265 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value46, value47, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (263 : Vertex) (269 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value48, value49, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (265 : Vertex) (267 : Vertex) (269 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value50, value51, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (268 : Vertex) (269 : Vertex) (332 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value50, value51, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (268 : Vertex) (269 : Vertex) (396 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 64 = false := by
  rw [value60, value61, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (322 : Vertex) (324 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value61, value62, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (322 : Vertex) (323 : Vertex) (330 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value77, value78, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value94, value95, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (482 : Vertex) (483 : Vertex) (490 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E090.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h⟩

end
end Snake9.Regrowth.E112090
