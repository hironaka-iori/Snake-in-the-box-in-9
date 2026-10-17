import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) + (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (l₂ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1446)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1437 q) 2 8 (meaning1330 q) (meaning1434 q) (meaning1446 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1434 = false ∨ valuation q 1446 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) + (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (l₂ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1446)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1437 q) 3 7 (meaning1331 q) (meaning1433 q) (meaning1446 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1433 = false ∨ valuation q 1446 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) + (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (l₂ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1446)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1437 q) 4 6 (meaning1332 q) (meaning1432 q) (meaning1446 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1432 = false ∨ valuation q 1446 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) + (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (l₂ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1446)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1437 q) 5 5 (meaning1333 q) (meaning1431 q) (meaning1446 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1431 = false ∨ valuation q 1446 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) + (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (l₂ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1334)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1446)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1437 q) 6 4 (meaning1334 q) (meaning1430 q) (meaning1446 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1430 = false ∨ valuation q 1446 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) + (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (l₂ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1446)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1437 q) 7 3 (meaning1335 q) (meaning1429 q) (meaning1446 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1429 = false ∨ valuation q 1446 = true := counterClause774 (baseVal q)

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false := by
  rw [value1446]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1437 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 8 = false ∨ valuation q 9 = false := by
  rw [value1, value2, value8, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (64 : Vertex) (65 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 22 = false ∨ valuation q 24 = false := by
  rw [value16, value18, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (134 : Vertex) (138 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value20, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (136 : Vertex) (138 : Vertex) (140 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 47 = false := by
  rw [value41, value43, value44, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (210 : Vertex) (214 : Vertex) (218 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value67, value69, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (338 : Vertex) (342 : Vertex) (346 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E175.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h⟩

end
end Snake9.Regrowth.E112175
