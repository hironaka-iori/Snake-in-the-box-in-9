import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 93 = false := by
  rw [value85, value87, value89, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (388 : Vertex) (392 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 203 = true ∨ valuation q 87 = true ∨ valuation q 89 = true ∨ valuation q 93 = true := by
  rw [value85, value87, value89, value93, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(388 : Vertex), (392 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (386 : Vertex) [(388 : Vertex), (392 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 204 = true ∨ valuation q 90 = true := by
  rw [value86, value90, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (384 : Vertex) [(394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 204 = true ∨ valuation q 85 = true := by
  rw [value85, value86, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(384 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (394 : Vertex) [(384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 31 = false ∨ valuation q 85 = false ∨ valuation q 91 = false := by
  rw [value31, value85, value87, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (384 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 91 = false ∨ valuation q 103 = false := by
  rw [value85, value87, value91, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (396 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 32 = false ∨ valuation q 73 = false ∨ valuation q 92 = false := by
  rw [value32, value73, value88, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 206 = true ∨ valuation q 32 = true ∨ valuation q 87 = true ∨ valuation q 92 = true := by
  rw [value32, value87, value88, value92, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(133 : Vertex), (388 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (261 : Vertex) [(133 : Vertex), (388 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 206 = true ∨ valuation q 32 = true ∨ valuation q 73 = true ∨ valuation q 87 = true := by
  rw [value32, value73, value87, value88, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(133 : Vertex), (261 : Vertex), (388 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (397 : Vertex) [(133 : Vertex), (261 : Vertex), (388 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 85 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value85, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (384 : Vertex) (394 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 85 = false ∨ valuation q 91 = false ∨ valuation q 106 = false := by
  rw [value85, value89, value91, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (384 : Vertex) (396 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 208 = true ∨ valuation q 35 = true ∨ valuation q 89 = true := by
  rw [value35, value89, value90, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(138 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (386 : Vertex) [(138 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 74 = false ∨ valuation q 87 = false ∨ valuation q 92 = false := by
  rw [value74, value87, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (388 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 74 = false ∨ valuation q 87 = false ∨ valuation q 98 = false := by
  rw [value74, value87, value91, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (388 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 74 = false ∨ valuation q 89 = false ∨ valuation q 92 = false := by
  rw [value74, value89, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (392 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 74 = false ∨ valuation q 89 = false ∨ valuation q 98 = false := by
  rw [value74, value89, value91, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (392 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 74 = false ∨ valuation q 92 = false ∨ valuation q 98 = false := by
  rw [value74, value91, value92, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 98 = false := by
  rw [value87, value89, value91, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (392 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 87 = false ∨ valuation q 92 = false ∨ valuation q 98 = false := by
  rw [value87, value91, value92, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 89 = false ∨ valuation q 92 = false ∨ valuation q 98 = false := by
  rw [value89, value91, value92, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (392 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 210 = true ∨ valuation q 37 = true ∨ valuation q 91 = true := by
  rw [value37, value91, value92, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(141 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (389 : Vertex) [(141 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 210 = true ∨ valuation q 37 = true ∨ valuation q 88 = true := by
  rw [value37, value88, value92, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(141 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (396 : Vertex) [(141 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 40 = false ∨ valuation q 85 = false ∨ valuation q 94 = false := by
  rw [value40, value85, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (144 : Vertex) (384 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 40 = true ∨ valuation q 85 = true := by
  rw [value40, value85, value93, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(144 : Vertex), (384 : Vertex)] := by decide
  have hg := other_cover q (400 : Vertex) (401 : Vertex) [(144 : Vertex), (384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 94 = true := by
  rw [value94, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (401 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 93 = true ∨ valuation q 95 = true := by
  rw [value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ∈ [(400 : Vertex), (403 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (401 : Vertex) [(400 : Vertex), (403 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 93 = false ∨ valuation q 95 = false := by
  rw [value93, value95, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (401 : Vertex) (400 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide)

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 93 = true := by
  rw [value93, value94, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(400 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (403 : Vertex) [(400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value94, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (401 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 213 = true ∨ valuation q 96 = true ∨ valuation q 97 = true := by
  rw [value95, value96, value97, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(407 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (401 : Vertex) [(407 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 213 = true ∨ valuation q 94 = true ∨ valuation q 97 = true := by
  rw [value94, value95, value97, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(401 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (407 : Vertex) [(401 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 213 = true ∨ valuation q 94 = true ∨ valuation q 96 = true := by
  rw [value94, value95, value96, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(401 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (411 : Vertex) [(401 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block18 (q : Snake 81) (h : Conditions q) : B112E158.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112158
