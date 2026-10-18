import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 200 = true ∨ valuation q 5 = true ∨ valuation q 74 = true ∨ valuation q 85 = true := by
  rw [value5, value73, value74, value85, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(8 : Vertex), (265 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (268 : Vertex) [(8 : Vertex), (265 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 200 = true ∨ valuation q 5 = true ∨ valuation q 74 = true ∨ valuation q 76 = true := by
  rw [value5, value73, value74, value76, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(8 : Vertex), (265 : Vertex), (268 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (280 : Vertex) [(8 : Vertex), (265 : Vertex), (268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 73 = true ∨ valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 86 = true := by
  rw [value73, value74, value75, value77, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ∈ [(264 : Vertex), (267 : Vertex), (269 : Vertex), (281 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (265 : Vertex) [(264 : Vertex), (267 : Vertex), (269 : Vertex), (281 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 73 = false ∨ valuation q 75 = false ∨ valuation q 77 = false := by
  rw [value73, value74, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (264 : Vertex) (267 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 73 = false ∨ valuation q 75 = false ∨ valuation q 86 = false := by
  rw [value73, value74, value75, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (264 : Vertex) (267 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 73 = false ∨ valuation q 77 = false ∨ valuation q 86 = false := by
  rw [value73, value74, value77, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (264 : Vertex) (269 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 86 = false := by
  rw [value74, value75, value77, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (267 : Vertex) (269 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value73, value75, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (265 : Vertex) (264 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 73 = false ∨ valuation q 77 = false := by
  rw [value73, value77, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (265 : Vertex) (264 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 201 = true ∨ valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 86 = true := by
  rw [value74, value75, value77, value86, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(267 : Vertex), (269 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (264 : Vertex) [(267 : Vertex), (269 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 201 = true ∨ valuation q 73 = true ∨ valuation q 77 = true ∨ valuation q 86 = true := by
  rw [value73, value74, value77, value86, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(264 : Vertex), (269 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (267 : Vertex) [(264 : Vertex), (269 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 201 = true ∨ valuation q 73 = true ∨ valuation q 75 = true ∨ valuation q 86 = true := by
  rw [value73, value74, value75, value86, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(264 : Vertex), (267 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (269 : Vertex) [(264 : Vertex), (267 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 68 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value68, value74, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (265 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 68 = false ∨ valuation q 74 = false ∨ valuation q 88 = false := by
  rw [value68, value74, value75, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (265 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 68 = false ∨ valuation q 78 = false ∨ valuation q 88 = false := by
  rw [value68, value75, value78, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (271 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 78 = false ∨ valuation q 88 = false := by
  rw [value74, value75, value78, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (265 : Vertex) (271 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 202 = true ∨ valuation q 74 = true ∨ valuation q 78 = true ∨ valuation q 88 = true := by
  rw [value74, value75, value78, value88, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(265 : Vertex), (271 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (259 : Vertex) [(265 : Vertex), (271 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 202 = true ∨ valuation q 68 = true ∨ valuation q 78 = true ∨ valuation q 88 = true := by
  rw [value68, value75, value78, value88, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(259 : Vertex), (271 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (265 : Vertex) [(259 : Vertex), (271 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 202 = true ∨ valuation q 68 = true ∨ valuation q 74 = true ∨ valuation q 88 = true := by
  rw [value68, value74, value75, value88, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(259 : Vertex), (265 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (271 : Vertex) [(259 : Vertex), (265 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 202 = true ∨ valuation q 68 = true ∨ valuation q 74 = true ∨ valuation q 78 = true := by
  rw [value68, value74, value75, value78, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(259 : Vertex), (265 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (283 : Vertex) [(259 : Vertex), (265 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 76 = true := by
  rw [value76, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (268 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 7 = false ∨ valuation q 69 = false ∨ valuation q 73 = false := by
  rw [value7, value69, value73, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (260 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 7 = false ∨ valuation q 69 = false ∨ valuation q 77 = false := by
  rw [value7, value69, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (260 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 7 = false ∨ valuation q 69 = false ∨ valuation q 89 = false := by
  rw [value7, value69, value76, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (260 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 7 = false ∨ valuation q 69 = false ∨ valuation q 97 = false := by
  rw [value7, value69, value76, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (260 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 7 = false ∨ valuation q 69 = false ∨ valuation q 114 = false := by
  rw [value7, value69, value76, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (260 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 7 = false ∨ valuation q 73 = false ∨ valuation q 77 = false := by
  rw [value7, value73, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (264 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 7 = false ∨ valuation q 73 = false ∨ valuation q 89 = false := by
  rw [value7, value73, value76, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (264 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 7 = false ∨ valuation q 73 = false ∨ valuation q 97 = false := by
  rw [value7, value73, value76, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (264 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 7 = false ∨ valuation q 73 = false ∨ valuation q 114 = false := by
  rw [value7, value73, value76, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (264 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 7 = false ∨ valuation q 77 = false ∨ valuation q 89 = false := by
  rw [value7, value76, value77, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (269 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 7 = false ∨ valuation q 77 = false ∨ valuation q 97 = false := by
  rw [value7, value76, value77, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (269 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E057.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112057
