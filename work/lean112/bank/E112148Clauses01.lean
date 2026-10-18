import E112148Semantics
import B112E148Inputs
namespace Snake9.Regrowth.E112148
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 123 = true ∨ valuation q 4 = true ∨ valuation q 14 = true := by
  rw [value4, value12, value14, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(65 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (80 : Vertex) [(65 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 123 = true ∨ valuation q 4 = true ∨ valuation q 11 = true := by
  rw [value4, value11, value12, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(65 : Vertex), (80 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (83 : Vertex) [(65 : Vertex), (80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 13 = false := by
  rw [value6, value12, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (67 : Vertex) (81 : Vertex) (82 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 18 = false := by
  rw [value6, value12, value14, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (67 : Vertex) (81 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 18 = false := by
  rw [value12, value13, value14, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (81 : Vertex) (82 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 126 = true ∨ valuation q 11 = true ∨ valuation q 73 = true := by
  rw [value11, value15, value73, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(80 : Vertex), (340 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (92 : Vertex) [(80 : Vertex), (340 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 126 = true ∨ valuation q 11 = true ∨ valuation q 19 = true := by
  rw [value11, value15, value19, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(80 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (340 : Vertex) [(80 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 127 = true ∨ valuation q 17 = true ∨ valuation q 19 = true := by
  rw [value16, value17, value19, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(90 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (80 : Vertex) [(90 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 127 = true ∨ valuation q 11 = true ∨ valuation q 17 = true := by
  rw [value11, value16, value17, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(80 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (92 : Vertex) [(80 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 18 = false := by
  rw [value13, value16, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (82 : Vertex) (88 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 20 = false := by
  rw [value13, value16, value17, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (82 : Vertex) (88 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 53 = false := by
  rw [value13, value16, value17, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (82 : Vertex) (88 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value13, value17, value18, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (82 : Vertex) (91 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 13 = false ∨ valuation q 20 = false ∨ valuation q 53 = false := by
  rw [value13, value17, value20, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (82 : Vertex) (94 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value16, value17, value18, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (88 : Vertex) (91 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 53 = false := by
  rw [value16, value17, value18, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (88 : Vertex) (91 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 78 = false := by
  rw [value16, value17, value18, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (88 : Vertex) (91 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 16 = false ∨ valuation q 20 = false ∨ valuation q 53 = false := by
  rw [value16, value17, value20, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (88 : Vertex) (94 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 78 = false := by
  rw [value17, value18, value20, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (91 : Vertex) (94 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 8 = false ∨ valuation q 14 = false ∨ valuation q 17 = false := by
  rw [value8, value14, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (75 : Vertex) (83 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 8 = false ∨ valuation q 14 = false ∨ valuation q 21 = false := by
  rw [value8, value14, value18, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (75 : Vertex) (83 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 79 = false := by
  rw [value14, value17, value18, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (83 : Vertex) (90 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 20 = false := by
  rw [value15, value16, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (84 : Vertex) (88 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 131 = true ∨ valuation q 17 = true ∨ valuation q 21 = true := by
  rw [value17, value20, value21, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(90 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (92 : Vertex) [(90 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 131 = true ∨ valuation q 17 = true ∨ valuation q 19 = true := by
  rw [value17, value19, value20, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(90 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (95 : Vertex) [(90 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 10 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value10, value18, value20, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (79 : Vertex) (91 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 132 = true ∨ valuation q 10 = true ∨ valuation q 18 = true := by
  rw [value10, value18, value21, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(79 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (94 : Vertex) [(79 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 40 = false := by
  rw [value22, value24, value26, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (137 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 81 = false := by
  rw [value22, value24, value26, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (137 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 30 = false ∨ valuation q 40 = false := by
  rw [value22, value24, value30, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (145 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 26 = false ∨ valuation q 30 = false ∨ valuation q 40 = false := by
  rw [value22, value26, value30, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (137 : Vertex) (145 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 134 = true ∨ valuation q 31 = true := by
  rw [value23, value31, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(146 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (131 : Vertex) [(146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E148.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112148
