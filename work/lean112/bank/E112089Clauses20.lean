import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 193 = true ∨ valuation q 70 = true ∨ valuation q 74 = true := by
  rw [value69, value70, value74, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(209 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (210 : Vertex) [(209 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 193 = true ∨ valuation q 70 = true ∨ valuation q 71 = true := by
  rw [value69, value70, value71, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(209 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (216 : Vertex) [(209 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 46 = false ∨ valuation q 56 = false ∨ valuation q 69 = false := by
  rw [value46, value56, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (193 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 46 = false ∨ valuation q 56 = false ∨ valuation q 72 = false := by
  rw [value46, value56, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (193 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 46 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value46, value69, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (208 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 56 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value56, value69, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (193 : Vertex) (208 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 194 = true ∨ valuation q 46 = true ∨ valuation q 56 = true ∨ valuation q 72 = true := by
  rw [value46, value56, value70, value72, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(145 : Vertex), (193 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (208 : Vertex) [(145 : Vertex), (193 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 57 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value57, value69, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (208 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 57 = false ∨ valuation q 69 = false ∨ valuation q 73 = false := by
  rw [value57, value69, value71, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (208 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 57 = false ∨ valuation q 69 = false ∨ valuation q 75 = false := by
  rw [value57, value69, value71, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (208 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 57 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value57, value71, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (211 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 57 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value57, value71, value72, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (211 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 57 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value57, value71, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value69, value71, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (208 : Vertex) (211 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value69, value71, value72, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (208 : Vertex) (211 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 69 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value69, value71, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (208 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value71, value72, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (211 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 57 = true ∨ valuation q 72 = true ∨ valuation q 73 = true ∨ valuation q 75 = true := by
  rw [value57, value71, value72, value73, value75, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(194 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (208 : Vertex) [(194 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 57 = true ∨ valuation q 69 = true ∨ valuation q 73 = true ∨ valuation q 75 = true := by
  rw [value57, value69, value71, value73, value75, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(194 : Vertex), (208 : Vertex), (214 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (211 : Vertex) [(194 : Vertex), (208 : Vertex), (214 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 57 = true ∨ valuation q 69 = true ∨ valuation q 72 = true ∨ valuation q 75 = true := by
  rw [value57, value69, value71, value72, value75, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(194 : Vertex), (208 : Vertex), (211 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (214 : Vertex) [(194 : Vertex), (208 : Vertex), (211 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 72 = true := by
  rw [value72, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (211 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 28 = false ∨ valuation q 71 = false ∨ valuation q 116 = false := by
  rw [value28, value71, value72, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (210 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 58 = false ∨ valuation q 70 = false ∨ valuation q 116 = false := by
  rw [value58, value70, value72, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (195 : Vertex) (209 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 196 = true ∨ valuation q 58 = true ∨ valuation q 70 = true ∨ valuation q 71 = true ∨ valuation q 116 = true := by
  rw [value58, value70, value71, value72, value116, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(195 : Vertex), (209 : Vertex), (210 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (83 : Vertex) [(195 : Vertex), (209 : Vertex), (210 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 196 = true ∨ valuation q 28 = true ∨ valuation q 70 = true ∨ valuation q 71 = true ∨ valuation q 116 = true := by
  rw [value28, value70, value71, value72, value116, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(83 : Vertex), (209 : Vertex), (210 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (195 : Vertex) [(83 : Vertex), (209 : Vertex), (210 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 196 = true ∨ valuation q 28 = true ∨ valuation q 58 = true ∨ valuation q 70 = true ∨ valuation q 116 = true := by
  rw [value28, value58, value70, value72, value116, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(83 : Vertex), (195 : Vertex), (209 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (210 : Vertex) [(83 : Vertex), (195 : Vertex), (209 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 196 = true ∨ valuation q 28 = true ∨ valuation q 58 = true ∨ valuation q 70 = true ∨ valuation q 71 = true := by
  rw [value28, value58, value70, value71, value72, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(83 : Vertex), (195 : Vertex), (209 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (467 : Vertex) [(83 : Vertex), (195 : Vertex), (209 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 73 = true := by
  rw [value73, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (214 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 49 = true ∨ valuation q 60 = true ∨ valuation q 71 = true ∨ valuation q 78 = true := by
  rw [value49, value60, value71, value73, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ∈ [(150 : Vertex), (198 : Vertex), (210 : Vertex), (222 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (214 : Vertex) [(150 : Vertex), (198 : Vertex), (210 : Vertex), (222 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 49 = false ∨ valuation q 60 = false ∨ valuation q 71 = false := by
  rw [value49, value60, value71, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (214 : Vertex) (150 : Vertex) (198 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 49 = false ∨ valuation q 60 = false ∨ valuation q 78 = false := by
  rw [value49, value60, value73, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (214 : Vertex) (150 : Vertex) (198 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 49 = false ∨ valuation q 71 = false ∨ valuation q 78 = false := by
  rw [value49, value71, value73, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (214 : Vertex) (150 : Vertex) (210 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E089.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112089
