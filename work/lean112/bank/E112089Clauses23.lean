import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 53 = false ∨ valuation q 78 = false ∨ valuation q 121 = false := by
  rw [value53, value75, value78, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (222 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 71 = false ∨ valuation q 74 = false ∨ valuation q 121 = false := by
  rw [value71, value74, value75, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (210 : Vertex) (216 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 71 = false ∨ valuation q 78 = false ∨ valuation q 121 = false := by
  rw [value71, value75, value78, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (210 : Vertex) (222 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 78 = false ∨ valuation q 121 = false := by
  rw [value74, value75, value78, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (216 : Vertex) (222 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 199 = true ∨ valuation q 33 = true ∨ valuation q 53 = true ∨ valuation q 71 = true ∨ valuation q 74 = true ∨ valuation q 78 = true := by
  rw [value33, value53, value71, value74, value75, value78, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(90 : Vertex), (154 : Vertex), (210 : Vertex), (216 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (474 : Vertex) [(90 : Vertex), (154 : Vertex), (210 : Vertex), (216 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 76 = true := by
  rw [value76, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (220 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 65 = true ∨ valuation q 74 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value65, value74, value76, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ∈ [(204 : Vertex), (216 : Vertex), (221 : Vertex), (222 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (220 : Vertex) [(204 : Vertex), (216 : Vertex), (221 : Vertex), (222 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 65 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value65, value74, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (220 : Vertex) (204 : Vertex) (216 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value74, value76, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (220 : Vertex) (216 : Vertex) (221 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 74 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value74, value76, value77, value78, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(216 : Vertex), (221 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (204 : Vertex) [(216 : Vertex), (221 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 65 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value65, value76, value77, value78, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(204 : Vertex), (221 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (216 : Vertex) [(204 : Vertex), (221 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 65 = true ∨ valuation q 74 = true ∨ valuation q 78 = true := by
  rw [value65, value74, value76, value78, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(204 : Vertex), (216 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (221 : Vertex) [(204 : Vertex), (216 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 65 = true ∨ valuation q 74 = true ∨ valuation q 77 = true := by
  rw [value65, value74, value76, value77, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(204 : Vertex), (216 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (222 : Vertex) [(204 : Vertex), (216 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 66 = false ∨ valuation q 76 = false ∨ valuation q 123 = false := by
  rw [value66, value76, value77, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (205 : Vertex) (220 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 201 = true ∨ valuation q 76 = true ∨ valuation q 123 = true := by
  rw [value76, value77, value123, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(220 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (205 : Vertex) [(220 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 201 = true ∨ valuation q 66 = true ∨ valuation q 123 = true := by
  rw [value66, value77, value123, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(205 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (220 : Vertex) [(205 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 201 = true ∨ valuation q 66 = true ∨ valuation q 76 = true := by
  rw [value66, value76, value77, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (477 : Vertex) → w ∈ [(205 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (477 : Vertex) [(205 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 67 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value67, value73, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (206 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 67 = false ∨ valuation q 73 = false ∨ valuation q 76 = false := by
  rw [value67, value73, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (206 : Vertex) (214 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 67 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value67, value75, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (206 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 73 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value73, value75, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 73 = true ∨ valuation q 75 = true ∨ valuation q 76 = true := by
  rw [value73, value75, value76, value78, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(214 : Vertex), (218 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (206 : Vertex) [(214 : Vertex), (218 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 67 = true ∨ valuation q 75 = true ∨ valuation q 76 = true := by
  rw [value67, value75, value76, value78, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(206 : Vertex), (218 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (214 : Vertex) [(206 : Vertex), (218 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 67 = true ∨ valuation q 73 = true ∨ valuation q 76 = true := by
  rw [value67, value73, value76, value78, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(206 : Vertex), (214 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (218 : Vertex) [(206 : Vertex), (214 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 67 = true ∨ valuation q 73 = true ∨ valuation q 75 = true := by
  rw [value67, value73, value75, value78, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(206 : Vertex), (214 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (220 : Vertex) [(206 : Vertex), (214 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 79 = true := by
  rw [value79, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (259 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 203 = true ∨ valuation q 83 = true ∨ valuation q 92 = true := by
  rw [value79, value83, value92, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (3 : Vertex) → w ∈ [(323 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (3 : Vertex) [(323 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 203 = true ∨ valuation q 3 = true ∨ valuation q 92 = true := by
  rw [value3, value79, value92, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(3 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (323 : Vertex) [(3 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 203 = true ∨ valuation q 3 = true ∨ valuation q 83 = true := by
  rw [value3, value79, value83, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(3 : Vertex), (323 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (387 : Vertex) [(3 : Vertex), (323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 204 = true := by
  rw [value80, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (264 : Vertex) (266 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 7 = false ∨ valuation q 86 = false ∨ valuation q 95 = false := by
  rw [value7, value81, value86, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (10 : Vertex) (330 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 205 = true ∨ valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 86 = true ∨ valuation q 95 = true := by
  rw [value80, value81, value82, value86, value95, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(264 : Vertex), (282 : Vertex), (330 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (10 : Vertex) [(264 : Vertex), (282 : Vertex), (330 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block23 (q : Snake 81) (h : Conditions q) : B112E089.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112089
