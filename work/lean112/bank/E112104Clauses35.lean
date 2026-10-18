import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) + (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (l₂ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1689 q) 8 12 (meaning1538 q) (meaning1680 q) (meaning1708 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1680 = false ∨ valuation q 1708 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) + (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (l₂ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1689 q) 9 11 (meaning1539 q) (meaning1679 q) (meaning1708 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1679 = false ∨ valuation q 1708 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) + (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (l₂ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1689 q) 10 10 (meaning1540 q) (meaning1678 q) (meaning1708 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1678 = false ∨ valuation q 1708 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) + (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (l₂ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1689 q) 11 9 (meaning1541 q) (meaning1677 q) (meaning1708 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1677 = false ∨ valuation q 1708 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1676 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) + (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (l₂ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1676)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1689 q) 12 8 (meaning1542 q) (meaning1676 q) (meaning1708 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1676 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1676 = false ∨ valuation q 1708 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) + (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (l₂ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1675)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1689 q) 13 7 (meaning1543 q) (meaning1675 q) (meaning1708 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1675 = false ∨ valuation q 1708 = true := counterClause1126 (baseVal q)

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false := by
  rw [value1708]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1689 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value12, value13, value14, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (96 : Vertex) (98 : Vertex) (100 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 17 = false ∨ valuation q 18 = false := by
  rw [value12, value13, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (96 : Vertex) (98 : Vertex) (104 : Vertex) (106 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 20 = false ∨ valuation q 64 = false ∨ valuation q 69 = false := by
  rw [value14, value20, value64, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (100 : Vertex) (108 : Vertex) (356 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 21 = false := by
  rw [value17, value18, value20, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (104 : Vertex) (106 : Vertex) (108 : Vertex) (110 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value22, value23, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (113 : Vertex) (115 : Vertex) (121 : Vertex) (123 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 33 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value31, value33, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (227 : Vertex) (231 : Vertex) (483 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value34, value37, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (233 : Vertex) (237 : Vertex) (489 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 44 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value37, value44, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (237 : Vertex) (253 : Vertex) (493 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value64, value65, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (356 : Vertex) (357 : Vertex) (364 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 76 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value70, value76, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (365 : Vertex) (381 : Vertex) (493 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 77 = false := by
  rw [value73, value74, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (370 : Vertex) (374 : Vertex) (378 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value76, value78, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (381 : Vertex) (383 : Vertex) (509 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value81, value82, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (421 : Vertex) (428 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value84, value85, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (426 : Vertex) (427 : Vertex) (490 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value86, value87, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (428 : Vertex) (429 : Vertex) (492 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 93 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value87, value93, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (429 : Vertex) (445 : Vertex) (493 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 94 = false := by
  rw [value90, value91, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (434 : Vertex) (438 : Vertex) (442 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value96, value97, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (482 : Vertex) (484 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value96, value97, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (482 : Vertex) (488 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 106 = false := by
  rw [value96, value99, value102, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (484 : Vertex) (488 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value97, value98, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (482 : Vertex) (483 : Vertex) (490 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 100 = false ∨ valuation q 104 = false ∨ valuation q 108 = false := by
  rw [value97, value100, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (482 : Vertex) (486 : Vertex) (490 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value99, value100, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (484 : Vertex) (486 : Vertex) (492 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value102, value103, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (488 : Vertex) (489 : Vertex) (492 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value102, value103, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (488 : Vertex) (489 : Vertex) (504 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E104.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112104
