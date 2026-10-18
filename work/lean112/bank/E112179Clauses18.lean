import E112179Semantics
import B112E179Inputs
namespace Snake9.Regrowth.E112179
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1433 = true := by
  have hs : count1427 q = (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1433)) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 5 2 (meaning1375 q) (meaning1418 q) (meaning1433 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1418 = false ∨ valuation q 1433 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) + (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (l₂ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1446)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1437 q) 3 7 (meaning1331 q) (meaning1433 q) (meaning1446 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1433 = false ∨ valuation q 1446 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) + (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (l₂ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1446)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1437 q) 4 6 (meaning1332 q) (meaning1432 q) (meaning1446 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1432 = false ∨ valuation q 1446 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) + (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (l₂ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1446)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1437 q) 5 5 (meaning1333 q) (meaning1431 q) (meaning1446 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1431 = false ∨ valuation q 1446 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) + (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (l₂ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1334)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1446)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1437 q) 6 4 (meaning1334 q) (meaning1430 q) (meaning1446 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1430 = false ∨ valuation q 1446 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) + (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (l₂ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1446)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24, -26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1437 q) 7 3 (meaning1335 q) (meaning1429 q) (meaning1446 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1429 = false ∨ valuation q 1446 = true := counterClause582 (baseVal q)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false := by
  rw [value1446]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1437 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 11 = false ∨ valuation q 31 = false ∨ valuation q 35 = false := by
  rw [value8, value11, value31, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (64 : Vertex) (72 : Vertex) (192 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 11 = false ∨ valuation q 57 = false ∨ valuation q 61 = false := by
  rw [value8, value11, value57, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (64 : Vertex) (72 : Vertex) (320 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E179.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h⟩

end
end Snake9.Regrowth.E112179
