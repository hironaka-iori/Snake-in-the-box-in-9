import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 4 = false ∨ valuation q 83 = false ∨ valuation q 92 = false := by
  rw [value4, value82, value83, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (70 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 5 = false ∨ valuation q 79 = false ∨ valuation q 96 = false := by
  rw [value5, value79, value83, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (71 : Vertex) (323 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 5 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value5, value81, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (71 : Vertex) (325 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value79, value81, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (323 : Vertex) (325 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 96 = false := by
  rw [value79, value81, value83, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (323 : Vertex) (325 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 96 = false := by
  rw [value79, value82, value83, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (323 : Vertex) (326 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 96 = false := by
  rw [value81, value82, value83, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (325 : Vertex) (326 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 210 = true ∨ valuation q 79 = true ∨ valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 96 = true := by
  rw [value79, value81, value82, value83, value96, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(323 : Vertex), (325 : Vertex), (326 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (71 : Vertex) [(323 : Vertex), (325 : Vertex), (326 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 210 = true ∨ valuation q 5 = true ∨ valuation q 79 = true ∨ valuation q 81 = true ∨ valuation q 96 = true := by
  rw [value5, value79, value81, value83, value96, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(71 : Vertex), (323 : Vertex), (325 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (326 : Vertex) [(71 : Vertex), (323 : Vertex), (325 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 6 = false ∨ valuation q 85 = false := by
  rw [value6, value85, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (328 : Vertex) (72 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 6 = false ∨ valuation q 86 = false := by
  rw [value6, value86, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (328 : Vertex) (72 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 6 = false ∨ valuation q 108 = false := by
  rw [value6, value108, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (328 : Vertex) (72 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value85, value86, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (328 : Vertex) (329 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 85 = false ∨ valuation q 108 = false := by
  rw [value85, value108, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (328 : Vertex) (329 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 86 = false ∨ valuation q 108 = false := by
  rw [value86, value108, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (328 : Vertex) (330 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 84 = true := by
  rw [value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 211 = true := by
  rw [value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change BallClauseLogic.Endpoint q head
  exact (endpoint_iff q head).mpr (Or.inl h.head_fixed.symm)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 78 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value78, value84, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (328 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 84 = false ∨ valuation q 88 = false ∨ valuation q 97 = false := by
  rw [value84, value86, value88, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (328 : Vertex) (334 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 81 = false ∨ valuation q 98 = false ∨ valuation q 111 = false := by
  rw [value81, value87, value98, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (325 : Vertex) (365 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 98 = false ∨ valuation q 111 = false := by
  rw [value85, value87, value98, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (329 : Vertex) (365 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 214 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 111 = true := by
  rw [value81, value85, value87, value111, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (365 : Vertex) → w ∈ [(325 : Vertex), (329 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (365 : Vertex) [(325 : Vertex), (329 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 214 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 98 = true := by
  rw [value81, value85, value87, value98, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(325 : Vertex), (329 : Vertex), (365 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (461 : Vertex) [(325 : Vertex), (329 : Vertex), (365 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 215 = true ∨ valuation q 86 = true := by
  rw [value86, value88, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(330 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (326 : Vertex) [(330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 215 = true ∨ valuation q 82 = true := by
  rw [value82, value88, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(326 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (330 : Vertex) [(326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 89 = true := by
  rw [value89, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (337 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 11 = true ∨ valuation q 78 = true ∨ valuation q 91 = true := by
  rw [value11, value78, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ∈ [(81 : Vertex), (321 : Vertex), (341 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (337 : Vertex) [(81 : Vertex), (321 : Vertex), (341 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 11 = false ∨ valuation q 78 = false ∨ valuation q 91 = false := by
  rw [value11, value78, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (337 : Vertex) (81 : Vertex) (321 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 216 = true ∨ valuation q 78 = true ∨ valuation q 91 = true := by
  rw [value78, value89, value91, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (81 : Vertex) → w ∈ [(321 : Vertex), (341 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (81 : Vertex) [(321 : Vertex), (341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 216 = true ∨ valuation q 11 = true ∨ valuation q 91 = true := by
  rw [value11, value89, value91, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(81 : Vertex), (341 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (321 : Vertex) [(81 : Vertex), (341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 216 = true ∨ valuation q 11 = true ∨ valuation q 78 = true := by
  rw [value11, value78, value89, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(81 : Vertex), (321 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (341 : Vertex) [(81 : Vertex), (321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 92 = true ∨ valuation q 112 = true := by
  rw [value90, value92, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ∈ [(342 : Vertex), (466 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (338 : Vertex) [(342 : Vertex), (466 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block18 (q : Snake 81) (h : Conditions q) : B112E260.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112260
