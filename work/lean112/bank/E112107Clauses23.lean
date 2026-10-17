import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1563 = true := by
  have hs : count1551 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) + (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (l₂ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1563)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1551 q) 5 8 (meaning1427 q) (meaning1545 q) (meaning1563 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1545 = false ∨ valuation q 1563 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1563 = true := by
  have hs : count1551 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) + (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (l₂ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1563)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1551 q) 6 7 (meaning1428 q) (meaning1544 q) (meaning1563 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1544 = false ∨ valuation q 1563 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1563 = true := by
  have hs : count1551 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) + (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (l₂ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1563)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1551 q) 7 6 (meaning1429 q) (meaning1543 q) (meaning1563 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1543 = false ∨ valuation q 1563 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1563 = true := by
  have hs : count1551 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) + (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (l₂ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1563)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1551 q) 8 5 (meaning1430 q) (meaning1542 q) (meaning1563 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1542 = false ∨ valuation q 1563 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1563 = true := by
  have hs : count1551 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) + (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (l₂ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1563)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1551 q) 9 4 (meaning1431 q) (meaning1541 q) (meaning1563 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1541 = false ∨ valuation q 1563 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1563 = true := by
  have hs : count1551 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) + (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (l₂ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1563)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1551 q) 10 3 (meaning1432 q) (meaning1540 q) (meaning1563 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1540 = false ∨ valuation q 1563 = true := counterClause742 (baseVal q)

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false := by
  rw [value1563]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1551 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 43 = false ∨ valuation q 53 = false := by
  rw [value1, value6, value43, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (16 : Vertex) (256 : Vertex) (272 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 10 = false ∨ valuation q 13 = false := by
  rw [value8, value9, value10, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (18 : Vertex) (22 : Vertex) (26 : Vertex) (30 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 26 = false := by
  rw [value20, value22, value23, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (178 : Vertex) (182 : Vertex) (186 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 31 = false ∨ valuation q 32 = false := by
  rw [value27, value28, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (193 : Vertex) (200 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value43, value45, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (260 : Vertex) (272 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 50 = false ∨ valuation q 52 = false := by
  rw [value44, value46, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (262 : Vertex) (266 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value46, value47, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (262 : Vertex) (263 : Vertex) (326 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value57, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (281 : Vertex) (283 : Vertex) (285 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value63, value64, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (321 : Vertex) (325 : Vertex) (329 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value64, value66, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (325 : Vertex) (327 : Vertex) (333 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value80, value82, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (418 : Vertex) (422 : Vertex) (426 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value81, value82, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (422 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E107.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h⟩

end
end Snake9.Regrowth.E112107
