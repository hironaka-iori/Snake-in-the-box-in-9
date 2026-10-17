import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 131 = true ∨ valuation q 12 = true ∨ valuation q 18 = true := by
  rw [value12, value13, value18, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (102 : Vertex) → w ∈ [(96 : Vertex), (106 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (102 : Vertex) [(96 : Vertex), (106 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 131 = true ∨ valuation q 12 = true ∨ valuation q 16 = true := by
  rw [value12, value13, value16, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [(96 : Vertex), (102 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (106 : Vertex) [(96 : Vertex), (102 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 16 = false := by
  rw [value12, value14, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (100 : Vertex) (96 : Vertex) (101 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 20 = false := by
  rw [value12, value14, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (100 : Vertex) (96 : Vertex) (101 : Vertex) (108 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 32 = false := by
  rw [value12, value14, value15, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (100 : Vertex) (96 : Vertex) (101 : Vertex) (228 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 64 = false := by
  rw [value12, value14, value15, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (100 : Vertex) (96 : Vertex) (101 : Vertex) (356 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 20 = false := by
  rw [value14, value15, value16, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (100 : Vertex) (101 : Vertex) (102 : Vertex) (108 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 32 = false := by
  rw [value14, value15, value16, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (100 : Vertex) (101 : Vertex) (102 : Vertex) (228 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 64 = false := by
  rw [value14, value15, value16, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (100 : Vertex) (101 : Vertex) (102 : Vertex) (356 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 32 = false ∨ valuation q 64 = false := by
  rw [value14, value15, value32, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (100 : Vertex) (101 : Vertex) (228 : Vertex) (356 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 132 = true ∨ valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 20 = true ∨ valuation q 32 = true ∨ valuation q 64 = true := by
  rw [value14, value15, value16, value20, value32, value64, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (100 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(101 : Vertex), (102 : Vertex), (108 : Vertex), (228 : Vertex), (356 : Vertex)] := by decide
  have hg := other_cover q (100 : Vertex) (96 : Vertex) [(101 : Vertex), (102 : Vertex), (108 : Vertex), (228 : Vertex), (356 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 132 = true ∨ valuation q 12 = true ∨ valuation q 16 = true ∨ valuation q 20 = true ∨ valuation q 32 = true ∨ valuation q 64 = true := by
  rw [value12, value14, value16, value20, value32, value64, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (100 : Vertex) w → w ∈ region → w ≠ (101 : Vertex) → w ∈ [(96 : Vertex), (102 : Vertex), (108 : Vertex), (228 : Vertex), (356 : Vertex)] := by decide
  have hg := other_cover q (100 : Vertex) (101 : Vertex) [(96 : Vertex), (102 : Vertex), (108 : Vertex), (228 : Vertex), (356 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 5 = false ∨ valuation q 14 = false ∨ valuation q 24 = false := by
  rw [value5, value14, value15, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (101 : Vertex) (37 : Vertex) (100 : Vertex) (117 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 5 = false ∨ valuation q 14 = false ∨ valuation q 65 = false := by
  rw [value5, value14, value15, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (101 : Vertex) (37 : Vertex) (100 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 5 = false ∨ valuation q 24 = false ∨ valuation q 65 = false := by
  rw [value5, value15, value24, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (101 : Vertex) (37 : Vertex) (117 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 21 = false := by
  rw [value13, value14, value16, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (98 : Vertex) (100 : Vertex) (110 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 25 = false := by
  rw [value13, value14, value16, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (98 : Vertex) (100 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 25 = false := by
  rw [value13, value16, value21, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (98 : Vertex) (110 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 21 = false ∨ valuation q 25 = false := by
  rw [value14, value16, value21, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (100 : Vertex) (110 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 12 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value12, value17, value18, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (96 : Vertex) (106 : Vertex) (108 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 12 = false ∨ valuation q 18 = false ∨ valuation q 27 = false := by
  rw [value12, value17, value18, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (96 : Vertex) (106 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 12 = false ∨ valuation q 20 = false ∨ valuation q 27 = false := by
  rw [value12, value17, value20, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (96 : Vertex) (108 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 27 = false := by
  rw [value17, value18, value20, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (106 : Vertex) (108 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 135 = true ∨ valuation q 12 = true ∨ valuation q 18 = true ∨ valuation q 20 = true := by
  rw [value12, value17, value18, value20, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(96 : Vertex), (106 : Vertex), (108 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (120 : Vertex) [(96 : Vertex), (106 : Vertex), (108 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 18 = true := by
  rw [value18, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (106 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 17 = false := by
  rw [value6, value13, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (42 : Vertex) (98 : Vertex) (104 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 19 = false := by
  rw [value6, value13, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (42 : Vertex) (98 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 21 = false := by
  rw [value6, value13, value18, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (42 : Vertex) (98 : Vertex) (110 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 35 = false := by
  rw [value6, value13, value18, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (42 : Vertex) (98 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 67 = false := by
  rw [value6, value13, value18, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (42 : Vertex) (98 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 6 = false ∨ valuation q 17 = false ∨ valuation q 19 = false := by
  rw [value6, value17, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (42 : Vertex) (104 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 6 = false ∨ valuation q 17 = false ∨ valuation q 21 = false := by
  rw [value6, value17, value18, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (42 : Vertex) (104 : Vertex) (110 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E104.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112104
