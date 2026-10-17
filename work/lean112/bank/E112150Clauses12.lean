import E112150Semantics
import B112E150Inputs
namespace Snake9.Regrowth.E112150
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1469 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) + (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (l₂ := [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1469)) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1465 q) 2 3 (meaning1406 q) (meaning1455 q) (meaning1469 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1455 = false ∨ valuation q 1469 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1470 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) + (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (l₂ := [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1470)) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1465 q) 2 4 (meaning1406 q) (meaning1456 q) (meaning1470 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1456 = false ∨ valuation q 1470 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) + (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (l₂ := [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1471)) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1465 q) 2 5 (meaning1406 q) (meaning1457 q) (meaning1471 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1457 = false ∨ valuation q 1471 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1470 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) + (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (l₂ := [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1470)) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1465 q) 3 3 (meaning1407 q) (meaning1455 q) (meaning1470 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1455 = false ∨ valuation q 1470 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) + (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (l₂ := [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1471)) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1465 q) 3 4 (meaning1407 q) (meaning1456 q) (meaning1471 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1456 = false ∨ valuation q 1471 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) + (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (l₂ := [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1471)) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1465 q) 4 3 (meaning1408 q) (meaning1455 q) (meaning1471 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1455 = false ∨ valuation q 1471 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1488 = true := by
  have hs : count1477 q = (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26, -28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) + (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80, -81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26, -28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (l₂ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80, -81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1361)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1488)) (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26, -28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80, -81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1477 q) 5 7 (meaning1361 q) (meaning1471 q) (meaning1488 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1471 = false ∨ valuation q 1488 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1488 = true := by
  have hs : count1477 q = (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26, -28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) + (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80, -81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26, -28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (l₂ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80, -81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1488)) (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26, -28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80, -81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1477 q) 6 6 (meaning1362 q) (meaning1470 q) (meaning1488 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1470 = false ∨ valuation q 1488 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1488 = true := by
  have hs : count1477 q = (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26, -28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) + (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80, -81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26, -28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (l₂ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80, -81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1488)) (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26, -28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80, -81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1477 q) 7 5 (meaning1363 q) (meaning1469 q) (meaning1488 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1469 = false ∨ valuation q 1488 = true := counterClause393 (baseVal q)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false := by
  rw [value1488]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1477 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 19 = false := by
  rw [value12, value15, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (67 : Vertex) (71 : Vertex) (75 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value44, value47, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (227 : Vertex) (231 : Vertex) (235 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E150.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h⟩

end
end Snake9.Regrowth.E112150
