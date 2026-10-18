import E112225Semantics
import B112E225Inputs
namespace Snake9.Regrowth.E112225
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 177 = true ∨ valuation q 72 = true ∨ valuation q 75 = true := by
  rw [value72, value73, value75, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(384 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (394 : Vertex) [(384 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 72 = false ∨ valuation q 80 = false ∨ valuation q 84 = false := by
  rw [value72, value74, value80, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (396 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 178 = true ∨ valuation q 75 = true ∨ valuation q 80 = true ∨ valuation q 84 = true := by
  rw [value74, value75, value80, value84, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(390 : Vertex), (396 : Vertex), (404 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (384 : Vertex) [(390 : Vertex), (396 : Vertex), (404 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 178 = true ∨ valuation q 72 = true ∨ valuation q 75 = true ∨ valuation q 80 = true := by
  rw [value72, value74, value75, value80, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(384 : Vertex), (390 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (404 : Vertex) [(384 : Vertex), (390 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 76 = false := by
  rw [value73, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 81 = false := by
  rw [value73, value74, value75, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 73 = false ∨ valuation q 76 = false ∨ valuation q 81 = false := by
  rw [value73, value75, value76, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (391 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 73 = false ∨ valuation q 76 = false ∨ valuation q 92 = false := by
  rw [value73, value75, value76, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (391 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 81 = false := by
  rw [value74, value75, value76, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (388 : Vertex) (391 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 92 = false := by
  rw [value74, value75, value76, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (388 : Vertex) (391 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 81 = false ∨ valuation q 92 = false := by
  rw [value74, value75, value81, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (388 : Vertex) (398 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 81 = false ∨ valuation q 92 = false := by
  rw [value75, value76, value81, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (391 : Vertex) (398 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 180 = true ∨ valuation q 75 = true ∨ valuation q 86 = true ∨ valuation q 93 = true := by
  rw [value75, value76, value86, value93, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(390 : Vertex), (407 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (135 : Vertex) [(390 : Vertex), (407 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 180 = true ∨ valuation q 25 = true ∨ valuation q 75 = true ∨ valuation q 86 = true := by
  rw [value25, value75, value76, value86, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(135 : Vertex), (390 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (455 : Vertex) [(135 : Vertex), (390 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 72 = false ∨ valuation q 79 = false ∨ valuation q 94 = false := by
  rw [value72, value77, value79, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (384 : Vertex) (394 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 80 = false := by
  rw [value77, value78, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (393 : Vertex) (394 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 27 = false ∨ valuation q 77 = false ∨ valuation q 87 = false := by
  rw [value27, value77, value78, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (392 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 182 = true ∨ valuation q 77 = true ∨ valuation q 87 = true := by
  rw [value77, value78, value87, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (393 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(392 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (393 : Vertex) (137 : Vertex) [(392 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 73 = false ∨ valuation q 77 = false ∨ valuation q 81 = false := by
  rw [value73, value77, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 73 = false ∨ valuation q 77 = false ∨ valuation q 88 = false := by
  rw [value73, value77, value79, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (392 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 73 = false ∨ valuation q 81 = false ∨ valuation q 88 = false := by
  rw [value73, value79, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 77 = false ∨ valuation q 81 = false ∨ valuation q 88 = false := by
  rw [value77, value79, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 81 = false := by
  rw [value74, value77, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 185 = true ∨ valuation q 75 = true ∨ valuation q 79 = true ∨ valuation q 80 = true := by
  rw [value75, value79, value80, value81, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(390 : Vertex), (394 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (142 : Vertex) [(390 : Vertex), (394 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 185 = true ∨ valuation q 28 = true ∨ valuation q 75 = true ∨ valuation q 80 = true := by
  rw [value28, value75, value80, value81, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(142 : Vertex), (390 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (394 : Vertex) [(142 : Vertex), (390 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value82, value83, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (403 : Vertex) (405 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 32 = false ∨ valuation q 82 = false ∨ valuation q 97 = false := by
  rw [value32, value82, value83, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (147 : Vertex) (401 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 32 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value32, value83, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (147 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 32 = false ∨ valuation q 86 = false ∨ valuation q 97 = false := by
  rw [value32, value83, value86, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (147 : Vertex) (407 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 32 = false ∨ valuation q 89 = false ∨ valuation q 97 = false := by
  rw [value32, value83, value89, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (147 : Vertex) (411 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 97 = false := by
  rw [value83, value86, value89, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (407 : Vertex) (411 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 33 = false ∨ valuation q 74 = false ∨ valuation q 85 = false := by
  rw [value33, value74, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (404 : Vertex) (148 : Vertex) (388 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E225.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112225
