import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 786 = false ∨ valuationOf q 886 = false ∨ valuationOf q 900 = true := by
  have hs : count891 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) + (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (l₂ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (786)) (literal (valuationOf q) (886)) (literal (valuationOf q) (900)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count891 q) 4 6 (meaning786 q) (meaning886 q) (meaning900 q) hs
  change valuationOf q 786 = false ∨ valuationOf q 886 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 786 = false ∨ valuation q 886 = false ∨ valuation q 900 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 787 = false ∨ valuationOf q 885 = false ∨ valuationOf q 900 = true := by
  have hs : count891 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) + (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (l₂ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (787)) (literal (valuationOf q) (885)) (literal (valuationOf q) (900)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count891 q) 5 5 (meaning787 q) (meaning885 q) (meaning900 q) hs
  change valuationOf q 787 = false ∨ valuationOf q 885 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 787 = false ∨ valuation q 885 = false ∨ valuation q 900 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 883 = false ∨ valuationOf q 900 = true := by
  have hs : count891 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) + (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (l₂ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (883)) (literal (valuationOf q) (900)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count891 q) 7 3 (meaning789 q) (meaning883 q) (meaning900 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 883 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 883 = false ∨ valuation q 900 = true := counterClause515 (baseVal q)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 900 = false := by
  rw [value900]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count891 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value38, value39, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (174 : Vertex) (175 : Vertex) (430 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value73, value74, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (417 : Vertex) (419 : Vertex) (425 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value73, value75, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (417 : Vertex) (421 : Vertex) (425 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 81 = false ∨ valuation q 93 = false ∨ valuation q 97 = false := by
  rw [value76, value81, value93, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (423 : Vertex) (431 : Vertex) (487 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value82, value83, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (432 : Vertex) (434 : Vertex) (440 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E075.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h⟩

end
end Snake9.Regrowth.E112075
