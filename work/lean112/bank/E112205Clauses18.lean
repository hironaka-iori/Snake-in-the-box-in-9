import E112205Semantics
import B112E205Inputs
namespace Snake9.Regrowth.E112205
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1526 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1526)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1519 q) 4 4 (meaning1462 q) (meaning1510 q) (meaning1526 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1510 = false ∨ valuation q 1526 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1525 = true := by
  have hs : count1519 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) + (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (l₂ := [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1525)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]) (countLit q [-85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1519 q) 5 2 (meaning1463 q) (meaning1508 q) (meaning1525 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1508 = false ∨ valuation q 1525 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1542)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1531 q) 4 8 (meaning1414 q) (meaning1526 q) (meaning1542 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1526 = false ∨ valuation q 1542 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1542)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1531 q) 5 7 (meaning1415 q) (meaning1525 q) (meaning1542 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1525 = false ∨ valuation q 1542 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1542)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1531 q) 6 6 (meaning1416 q) (meaning1524 q) (meaning1542 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1524 = false ∨ valuation q 1542 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1542)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1531 q) 7 5 (meaning1417 q) (meaning1523 q) (meaning1542 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1523 = false ∨ valuation q 1542 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1542)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -97, -98, -99, -101, -104, -105, -106, -107]) (count1531 q) 9 3 (meaning1419 q) (meaning1521 q) (meaning1542 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1521 = false ∨ valuation q 1542 = true := counterClause583 (baseVal q)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false := by
  rw [value1542]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1531 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value13, value14, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value60, value61, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (354 : Vertex) (355 : Vertex) (362 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E205.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h⟩

end
end Snake9.Regrowth.E112205
