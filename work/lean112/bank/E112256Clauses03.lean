import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 15 = true := by
  rw [value15, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (90 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = true ∨ valuation q 32 = true ∨ valuation q 51 = true := by
  rw [value15, value17, value32, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ∈ [(94 : Vertex), (122 : Vertex), (218 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (90 : Vertex) [(94 : Vertex), (122 : Vertex), (218 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 32 = true ∨ valuation q 51 = true := by
  rw [value15, value32, value51, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(122 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (94 : Vertex) [(122 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 17 = true ∨ valuation q 51 = true := by
  rw [value15, value17, value51, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(94 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (122 : Vertex) [(94 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 17 = true ∨ valuation q 32 = true := by
  rw [value15, value17, value32, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(94 : Vertex), (122 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (218 : Vertex) [(94 : Vertex), (122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 18 = false ∨ valuation q 33 = false := by
  rw [value14, value16, value18, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (93 : Vertex) (89 : Vertex) (95 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 18 = false ∨ valuation q 53 = false := by
  rw [value14, value16, value18, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (93 : Vertex) (89 : Vertex) (95 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 18 = false ∨ valuation q 90 = false := by
  rw [value14, value16, value18, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (93 : Vertex) (89 : Vertex) (95 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 33 = false ∨ valuation q 53 = false := by
  rw [value14, value16, value33, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (93 : Vertex) (89 : Vertex) (125 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 33 = false ∨ valuation q 90 = false := by
  rw [value14, value16, value33, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (93 : Vertex) (89 : Vertex) (125 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 53 = false ∨ valuation q 90 = false := by
  rw [value14, value16, value53, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (93 : Vertex) (89 : Vertex) (221 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 33 = false ∨ valuation q 53 = false := by
  rw [value16, value18, value33, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (93 : Vertex) (95 : Vertex) (125 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 33 = false ∨ valuation q 90 = false := by
  rw [value16, value18, value33, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (93 : Vertex) (95 : Vertex) (125 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 53 = false ∨ valuation q 90 = false := by
  rw [value16, value18, value53, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (93 : Vertex) (95 : Vertex) (221 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 33 = false ∨ valuation q 53 = false ∨ valuation q 90 = false := by
  rw [value16, value33, value53, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (93 : Vertex) (125 : Vertex) (221 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 143 = true ∨ valuation q 18 = true ∨ valuation q 33 = true ∨ valuation q 53 = true ∨ valuation q 90 = true := by
  rw [value16, value18, value33, value53, value90, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(95 : Vertex), (125 : Vertex), (221 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (89 : Vertex) [(95 : Vertex), (125 : Vertex), (221 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 143 = true ∨ valuation q 14 = true ∨ valuation q 18 = true ∨ valuation q 53 = true ∨ valuation q 90 = true := by
  rw [value14, value16, value18, value53, value90, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(89 : Vertex), (95 : Vertex), (221 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (125 : Vertex) [(89 : Vertex), (95 : Vertex), (221 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 34 = false := by
  rw [value15, value17, value18, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (94 : Vertex) (90 : Vertex) (95 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 91 = false := by
  rw [value15, value17, value18, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (94 : Vertex) (90 : Vertex) (95 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 34 = false ∨ valuation q 91 = false := by
  rw [value15, value17, value34, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (94 : Vertex) (90 : Vertex) (126 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 34 = false ∨ valuation q 91 = false := by
  rw [value17, value18, value34, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (94 : Vertex) (95 : Vertex) (126 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 144 = true ∨ valuation q 18 = true ∨ valuation q 34 = true ∨ valuation q 91 = true := by
  rw [value17, value18, value34, value91, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(95 : Vertex), (126 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (90 : Vertex) [(95 : Vertex), (126 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 18 = true := by
  rw [value18, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (95 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 16 = false := by
  rw [value9, value13, value16, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (79 : Vertex) (87 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 17 = false := by
  rw [value9, value13, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (79 : Vertex) (87 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 35 = false := by
  rw [value9, value13, value18, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (79 : Vertex) (87 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 9 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value9, value16, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (79 : Vertex) (93 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 35 = false := by
  rw [value9, value17, value18, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (79 : Vertex) (94 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 54 = false := by
  rw [value9, value17, value18, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (79 : Vertex) (94 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 92 = false := by
  rw [value9, value17, value18, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (79 : Vertex) (94 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value13, value16, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (87 : Vertex) (93 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 13 = false ∨ valuation q 17 = false ∨ valuation q 35 = false := by
  rw [value13, value17, value18, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (87 : Vertex) (94 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E256.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112256
