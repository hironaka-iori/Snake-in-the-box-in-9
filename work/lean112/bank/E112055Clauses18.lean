import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 121 = false := by
  rw [value81, value82, value84, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (274 : Vertex) (276 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value81, value84, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (274 : Vertex) (279 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 121 = false := by
  rw [value81, value84, value85, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (274 : Vertex) (279 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 102 = false ∨ valuation q 121 = false := by
  rw [value81, value84, value102, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (274 : Vertex) (342 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value82, value84, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (276 : Vertex) (279 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 121 = false := by
  rw [value82, value84, value85, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (276 : Vertex) (279 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 102 = false ∨ valuation q 121 = false := by
  rw [value82, value84, value102, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (276 : Vertex) (342 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 102 = false ∨ valuation q 121 = false := by
  rw [value84, value85, value102, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (279 : Vertex) (342 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 212 = true ∨ valuation q 14 = true ∨ valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 102 = true ∨ valuation q 121 = true := by
  rw [value14, value81, value82, value84, value85, value102, value121, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(22 : Vertex), (274 : Vertex), (276 : Vertex), (279 : Vertex), (342 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (262 : Vertex) [(22 : Vertex), (274 : Vertex), (276 : Vertex), (279 : Vertex), (342 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 212 = true ∨ valuation q 14 = true ∨ valuation q 72 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 102 = true ∨ valuation q 121 = true := by
  rw [value14, value72, value82, value84, value85, value102, value121, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(22 : Vertex), (262 : Vertex), (276 : Vertex), (279 : Vertex), (342 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (274 : Vertex) [(22 : Vertex), (262 : Vertex), (276 : Vertex), (279 : Vertex), (342 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 212 = true ∨ valuation q 14 = true ∨ valuation q 72 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 102 = true ∨ valuation q 121 = true := by
  rw [value14, value72, value81, value84, value85, value102, value121, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(22 : Vertex), (262 : Vertex), (274 : Vertex), (279 : Vertex), (342 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (276 : Vertex) [(22 : Vertex), (262 : Vertex), (274 : Vertex), (279 : Vertex), (342 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 212 = true ∨ valuation q 14 = true ∨ valuation q 72 = true ∨ valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 102 = true ∨ valuation q 121 = true := by
  rw [value14, value72, value81, value82, value84, value102, value121, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(22 : Vertex), (262 : Vertex), (274 : Vertex), (276 : Vertex), (342 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (279 : Vertex) [(22 : Vertex), (262 : Vertex), (274 : Vertex), (276 : Vertex), (342 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 212 = true ∨ valuation q 14 = true ∨ valuation q 72 = true ∨ valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 121 = true := by
  rw [value14, value72, value81, value82, value84, value85, value121, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(22 : Vertex), (262 : Vertex), (274 : Vertex), (276 : Vertex), (279 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (342 : Vertex) [(22 : Vertex), (262 : Vertex), (274 : Vertex), (276 : Vertex), (279 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 212 = true ∨ valuation q 14 = true ∨ valuation q 72 = true ∨ valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 102 = true := by
  rw [value14, value72, value81, value82, value84, value85, value102, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(22 : Vertex), (262 : Vertex), (274 : Vertex), (276 : Vertex), (279 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (406 : Vertex) [(22 : Vertex), (262 : Vertex), (274 : Vertex), (276 : Vertex), (279 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 73 = false ∨ valuation q 83 = false := by
  rw [value15, value73, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (263 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 73 = false ∨ valuation q 84 = false := by
  rw [value15, value73, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (263 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 73 = false ∨ valuation q 91 = false := by
  rw [value15, value73, value85, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (263 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 73 = false ∨ valuation q 103 = false := by
  rw [value15, value73, value85, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (263 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 73 = false ∨ valuation q 122 = false := by
  rw [value15, value73, value85, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (263 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value15, value83, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (277 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 83 = false ∨ valuation q 103 = false := by
  rw [value15, value83, value85, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (277 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 84 = false ∨ valuation q 103 = false := by
  rw [value15, value84, value85, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (278 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 73 = false ∨ valuation q 83 = false ∨ valuation q 91 = false := by
  rw [value73, value83, value85, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (277 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 73 = false ∨ valuation q 83 = false ∨ valuation q 103 = false := by
  rw [value73, value83, value85, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (277 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 73 = false ∨ valuation q 83 = false ∨ valuation q 122 = false := by
  rw [value73, value83, value85, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (277 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 73 = false ∨ valuation q 84 = false ∨ valuation q 91 = false := by
  rw [value73, value84, value85, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (278 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 73 = false ∨ valuation q 84 = false ∨ valuation q 103 = false := by
  rw [value73, value84, value85, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (278 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 73 = false ∨ valuation q 84 = false ∨ valuation q 122 = false := by
  rw [value73, value84, value85, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (278 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 73 = false ∨ valuation q 103 = false ∨ valuation q 122 = false := by
  rw [value73, value85, value103, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (343 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 84 = false ∨ valuation q 91 = false ∨ valuation q 103 = false := by
  rw [value84, value85, value91, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (278 : Vertex) (287 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 84 = false ∨ valuation q 91 = false ∨ valuation q 122 = false := by
  rw [value84, value85, value91, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (278 : Vertex) (287 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 84 = false ∨ valuation q 103 = false ∨ valuation q 122 = false := by
  rw [value84, value85, value103, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (278 : Vertex) (343 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E055.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112055
