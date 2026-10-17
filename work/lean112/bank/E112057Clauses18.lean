import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 70 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value70, value77, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (333 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 98 = false := by
  rw [value74, value76, value77, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (268 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 115 = false := by
  rw [value74, value76, value77, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (268 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 74 = false ∨ valuation q 78 = false ∨ valuation q 115 = false := by
  rw [value74, value77, value78, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (271 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 74 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value74, value77, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (333 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 98 = false := by
  rw [value76, value77, value78, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (268 : Vertex) (271 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 115 = false := by
  rw [value76, value77, value78, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (268 : Vertex) (271 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 76 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value76, value77, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (268 : Vertex) (333 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value77, value78, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (271 : Vertex) (333 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 204 = true ∨ valuation q 70 = true ∨ valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 98 = true ∨ valuation q 115 = true := by
  rw [value70, value76, value77, value78, value98, value115, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (269 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(261 : Vertex), (268 : Vertex), (271 : Vertex), (333 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (269 : Vertex) (265 : Vertex) [(261 : Vertex), (268 : Vertex), (271 : Vertex), (333 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 204 = true ∨ valuation q 70 = true ∨ valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 98 = true ∨ valuation q 115 = true := by
  rw [value70, value74, value76, value77, value98, value115, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (269 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(261 : Vertex), (265 : Vertex), (268 : Vertex), (333 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (269 : Vertex) (271 : Vertex) [(261 : Vertex), (265 : Vertex), (268 : Vertex), (333 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 204 = true ∨ valuation q 70 = true ∨ valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 115 = true := by
  rw [value70, value74, value76, value77, value78, value115, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (269 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(261 : Vertex), (265 : Vertex), (268 : Vertex), (271 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (269 : Vertex) (333 : Vertex) [(261 : Vertex), (265 : Vertex), (268 : Vertex), (271 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 204 = true ∨ valuation q 70 = true ∨ valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 98 = true := by
  rw [value70, value74, value76, value77, value78, value98, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (269 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(261 : Vertex), (265 : Vertex), (268 : Vertex), (271 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (269 : Vertex) (397 : Vertex) [(261 : Vertex), (265 : Vertex), (268 : Vertex), (271 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 9 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value9, value72, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 9 = false ∨ valuation q 72 = false ∨ valuation q 77 = false := by
  rw [value9, value72, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 9 = false ∨ valuation q 72 = false ∨ valuation q 90 = false := by
  rw [value9, value72, value78, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 9 = false ∨ valuation q 75 = false ∨ valuation q 77 = false := by
  rw [value9, value75, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (267 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 9 = false ∨ valuation q 75 = false ∨ valuation q 90 = false := by
  rw [value9, value75, value78, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (267 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 9 = false ∨ valuation q 77 = false ∨ valuation q 90 = false := by
  rw [value9, value77, value78, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (269 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 72 = false ∨ valuation q 75 = false ∨ valuation q 77 = false := by
  rw [value72, value75, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 72 = false ∨ valuation q 75 = false ∨ valuation q 90 = false := by
  rw [value72, value75, value78, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 72 = false ∨ valuation q 77 = false ∨ valuation q 90 = false := by
  rw [value72, value77, value78, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (269 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 90 = false := by
  rw [value75, value77, value78, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (269 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 9 = false ∨ valuation q 75 = false := by
  rw [value9, value75, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (271 : Vertex) (15 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide)

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 9 = false ∨ valuation q 77 = false := by
  rw [value9, value77, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (271 : Vertex) (15 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 9 = false ∨ valuation q 90 = false := by
  rw [value9, value90, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (271 : Vertex) (15 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide)

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value72, value75, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide)

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 205 = true ∨ valuation q 72 = true ∨ valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 90 = true := by
  rw [value72, value75, value77, value78, value90, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(263 : Vertex), (267 : Vertex), (269 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (15 : Vertex) [(263 : Vertex), (267 : Vertex), (269 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 205 = true ∨ valuation q 9 = true ∨ valuation q 72 = true ∨ valuation q 77 = true ∨ valuation q 90 = true := by
  rw [value9, value72, value77, value78, value90, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(15 : Vertex), (263 : Vertex), (269 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (267 : Vertex) [(15 : Vertex), (263 : Vertex), (269 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value79, value80, value81, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (274 : Vertex) (276 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 100 = false := by
  rw [value79, value81, value85, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (276 : Vertex) (280 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 117 = false := by
  rw [value79, value81, value85, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (276 : Vertex) (280 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E057.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112057
