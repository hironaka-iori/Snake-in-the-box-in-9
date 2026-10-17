import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 14 = false ∨ valuation q 70 = false := by
  rw [value14, value70, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (264 : Vertex) (268 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 133 = true ∨ valuation q 12 = true ∨ valuation q 70 = true := by
  rw [value11, value12, value70, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(265 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (268 : Vertex) [(265 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 133 = true ∨ valuation q 12 = true ∨ valuation q 14 = true := by
  rw [value11, value12, value14, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(265 : Vertex), (268 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (392 : Vertex) [(265 : Vertex), (268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 11 = false ∨ valuation q 13 = false := by
  rw [value6, value11, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (264 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 11 = false ∨ valuation q 20 = false := by
  rw [value6, value11, value12, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (264 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 11 = false ∨ valuation q 28 = false := by
  rw [value6, value11, value12, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (264 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 11 = false ∨ valuation q 46 = false := by
  rw [value6, value11, value12, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (264 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 11 = false ∨ valuation q 71 = false := by
  rw [value6, value11, value12, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (264 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 20 = false := by
  rw [value6, value12, value13, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (267 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 46 = false := by
  rw [value6, value12, value13, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (267 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 71 = false := by
  rw [value6, value12, value13, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (267 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 20 = false ∨ valuation q 28 = false := by
  rw [value6, value12, value20, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (281 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 28 = false ∨ valuation q 46 = false := by
  rw [value6, value12, value28, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (297 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 28 = false ∨ valuation q 71 = false := by
  rw [value6, value12, value28, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (297 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 20 = false := by
  rw [value11, value12, value13, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (264 : Vertex) (267 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 71 = false := by
  rw [value11, value12, value13, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (264 : Vertex) (267 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 20 = false ∨ valuation q 46 = false := by
  rw [value11, value12, value20, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (264 : Vertex) (281 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 20 = false ∨ valuation q 71 = false := by
  rw [value12, value13, value20, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (267 : Vertex) (281 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 29 = false := by
  rw [value12, value13, value15, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (265 : Vertex) (271 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 135 = true ∨ valuation q 15 = true ∨ valuation q 29 = true := by
  rw [value13, value15, value29, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(271 : Vertex), (299 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (265 : Vertex) [(271 : Vertex), (299 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 135 = true ∨ valuation q 12 = true ∨ valuation q 29 = true := by
  rw [value12, value13, value29, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(265 : Vertex), (299 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (271 : Vertex) [(265 : Vertex), (299 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 135 = true ∨ valuation q 12 = true ∨ valuation q 15 = true := by
  rw [value12, value13, value15, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(265 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (299 : Vertex) [(265 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 11 = false ∨ valuation q 30 = false ∨ valuation q 72 = false := by
  rw [value11, value14, value30, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (264 : Vertex) (300 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 136 = true ∨ valuation q 30 = true ∨ valuation q 72 = true := by
  rw [value14, value30, value72, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(300 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (264 : Vertex) [(300 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 136 = true ∨ valuation q 11 = true ∨ valuation q 72 = true := by
  rw [value11, value14, value72, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (300 : Vertex) → w ∈ [(264 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (300 : Vertex) [(264 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 136 = true ∨ valuation q 11 = true ∨ valuation q 30 = true := by
  rw [value11, value14, value30, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(264 : Vertex), (300 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (396 : Vertex) [(264 : Vertex), (300 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 10 = false ∨ valuation q 13 = false ∨ valuation q 23 = false := by
  rw [value10, value13, value15, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 10 = false ∨ valuation q 23 = false ∨ valuation q 73 = false := by
  rw [value10, value15, value23, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (287 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 137 = true ∨ valuation q 13 = true ∨ valuation q 23 = true ∨ valuation q 73 = true := by
  rw [value13, value15, value23, value73, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(267 : Vertex), (287 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (263 : Vertex) [(267 : Vertex), (287 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 137 = true ∨ valuation q 10 = true ∨ valuation q 23 = true ∨ valuation q 73 = true := by
  rw [value10, value15, value23, value73, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(263 : Vertex), (287 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (267 : Vertex) [(263 : Vertex), (287 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 137 = true ∨ valuation q 10 = true ∨ valuation q 13 = true ∨ valuation q 73 = true := by
  rw [value10, value13, value15, value73, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(263 : Vertex), (267 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (287 : Vertex) [(263 : Vertex), (267 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 137 = true ∨ valuation q 10 = true ∨ valuation q 13 = true ∨ valuation q 23 = true := by
  rw [value10, value13, value15, value23, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(263 : Vertex), (267 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (399 : Vertex) [(263 : Vertex), (267 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E254.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112254
