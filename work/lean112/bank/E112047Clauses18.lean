import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 87 = true ∨ valuation q 95 = true ∨ valuation q 98 = true := by
  rw [value87, value95, value97, value98, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(394 : Vertex), (408 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (154 : Vertex) [(394 : Vertex), (408 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 29 = true ∨ valuation q 95 = true ∨ valuation q 98 = true := by
  rw [value29, value95, value97, value98, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(154 : Vertex), (408 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (394 : Vertex) [(154 : Vertex), (408 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 29 = true ∨ valuation q 87 = true ∨ valuation q 98 = true := by
  rw [value29, value87, value97, value98, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(154 : Vertex), (394 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (408 : Vertex) [(154 : Vertex), (394 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 29 = true ∨ valuation q 87 = true ∨ valuation q 95 = true := by
  rw [value29, value87, value95, value97, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(154 : Vertex), (394 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (411 : Vertex) [(154 : Vertex), (394 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 91 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value91, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (403 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 216 = true ∨ valuation q 91 = true ∨ valuation q 96 = true := by
  rw [value91, value96, value98, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(403 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (410 : Vertex) [(403 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 96 = true := by
  rw [value96, value99, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(409 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (405 : Vertex) [(409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 92 = true := by
  rw [value92, value99, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(405 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (409 : Vertex) [(405 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 64 = false ∨ valuation q 80 = false ∨ valuation q 101 = false := by
  rw [value64, value80, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (386 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 64 = false ∨ valuation q 80 = false ∨ valuation q 105 = false := by
  rw [value64, value80, value100, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (386 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 64 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value64, value100, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (451 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 64 = false ∨ valuation q 105 = false ∨ valuation q 111 = false := by
  rw [value64, value100, value105, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (458 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 80 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value80, value100, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (451 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 80 = false ∨ valuation q 101 = false ∨ valuation q 111 = false := by
  rw [value80, value100, value101, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (451 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 80 = false ∨ valuation q 105 = false ∨ valuation q 111 = false := by
  rw [value80, value100, value105, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (458 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 105 = false ∨ valuation q 111 = false := by
  rw [value100, value101, value105, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (451 : Vertex) (458 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 218 = true ∨ valuation q 64 = true ∨ valuation q 101 = true ∨ valuation q 105 = true ∨ valuation q 111 = true := by
  rw [value64, value100, value101, value105, value111, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(322 : Vertex), (451 : Vertex), (458 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (386 : Vertex) [(322 : Vertex), (451 : Vertex), (458 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 218 = true ∨ valuation q 64 = true ∨ valuation q 80 = true ∨ valuation q 105 = true ∨ valuation q 111 = true := by
  rw [value64, value80, value100, value105, value111, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(322 : Vertex), (386 : Vertex), (458 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (451 : Vertex) [(322 : Vertex), (386 : Vertex), (458 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 218 = true ∨ valuation q 64 = true ∨ valuation q 80 = true ∨ valuation q 101 = true ∨ valuation q 111 = true := by
  rw [value64, value80, value100, value101, value111, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(322 : Vertex), (386 : Vertex), (451 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (458 : Vertex) [(322 : Vertex), (386 : Vertex), (451 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 101 = true := by
  rw [value101, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (451 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 81 = true ∨ valuation q 100 = true ∨ valuation q 106 = true ∨ valuation q 112 = true := by
  rw [value81, value100, value101, value106, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ∈ [(387 : Vertex), (450 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (451 : Vertex) [(387 : Vertex), (450 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 106 = false ∨ valuation q 112 = false := by
  rw [value106, value112, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (451 : Vertex) (459 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide)

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 219 = true ∨ valuation q 100 = true ∨ valuation q 106 = true ∨ valuation q 112 = true := by
  rw [value100, value101, value106, value112, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(450 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (387 : Vertex) [(450 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 219 = true ∨ valuation q 81 = true ∨ valuation q 106 = true ∨ valuation q 112 = true := by
  rw [value81, value101, value106, value112, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(387 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (450 : Vertex) [(387 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 219 = true ∨ valuation q 81 = true ∨ valuation q 100 = true ∨ valuation q 112 = true := by
  rw [value81, value100, value101, value112, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(387 : Vertex), (450 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (459 : Vertex) [(387 : Vertex), (450 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 219 = true ∨ valuation q 81 = true ∨ valuation q 100 = true ∨ valuation q 106 = true := by
  rw [value81, value100, value101, value106, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(387 : Vertex), (450 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (467 : Vertex) [(387 : Vertex), (450 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 82 = false ∨ valuation q 103 = false ∨ valuation q 113 = false := by
  rw [value82, value102, value103, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (388 : Vertex) (453 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 220 = true ∨ valuation q 82 = true ∨ valuation q 113 = true := by
  rw [value82, value102, value113, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (452 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(388 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (452 : Vertex) (453 : Vertex) [(388 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 103 = true := by
  rw [value103, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (453 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 102 = true ∨ valuation q 107 = true := by
  rw [value102, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ∈ [(452 : Vertex), (461 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (453 : Vertex) [(452 : Vertex), (461 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 221 = true ∨ valuation q 107 = true := by
  rw [value103, value107, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (452 : Vertex) [(461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 221 = true ∨ valuation q 102 = true := by
  rw [value102, value103, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(452 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (461 : Vertex) [(452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block18 (q : Snake 81) (h : Conditions q) : B112E047.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112047
