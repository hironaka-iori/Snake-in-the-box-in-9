import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 60 = false ∨ valuation q 71 = false ∨ valuation q 78 = false := by
  rw [value60, value71, value73, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (214 : Vertex) (198 : Vertex) (210 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 49 = false ∨ valuation q 60 = false := by
  rw [value49, value60, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (214 : Vertex) (150 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide)

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 49 = false ∨ valuation q 71 = false := by
  rw [value49, value71, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (214 : Vertex) (150 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 49 = false ∨ valuation q 78 = false := by
  rw [value49, value78, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (214 : Vertex) (150 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide)

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 197 = true ∨ valuation q 60 = true ∨ valuation q 71 = true ∨ valuation q 78 = true := by
  rw [value60, value71, value73, value78, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(198 : Vertex), (210 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (150 : Vertex) [(198 : Vertex), (210 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 197 = true ∨ valuation q 49 = true ∨ valuation q 71 = true ∨ valuation q 78 = true := by
  rw [value49, value71, value73, value78, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(150 : Vertex), (210 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (198 : Vertex) [(150 : Vertex), (210 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 197 = true ∨ valuation q 49 = true ∨ valuation q 60 = true ∨ valuation q 78 = true := by
  rw [value49, value60, value73, value78, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(150 : Vertex), (198 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (210 : Vertex) [(150 : Vertex), (198 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 197 = true ∨ valuation q 49 = true ∨ valuation q 60 = true ∨ valuation q 71 = true := by
  rw [value49, value60, value71, value73, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(150 : Vertex), (198 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (222 : Vertex) [(150 : Vertex), (198 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 51 = false ∨ valuation q 62 = false := by
  rw [value32, value51, value62, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (152 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 51 = false ∨ valuation q 69 = false := by
  rw [value32, value51, value69, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (152 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 51 = false ∨ valuation q 75 = false := by
  rw [value32, value51, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (152 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 51 = false ∨ valuation q 76 = false := by
  rw [value32, value51, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (152 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 51 = false ∨ valuation q 120 = false := by
  rw [value32, value51, value74, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (152 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 62 = false ∨ valuation q 69 = false := by
  rw [value32, value62, value69, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (200 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 62 = false ∨ valuation q 75 = false := by
  rw [value32, value62, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (200 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 62 = false ∨ valuation q 76 = false := by
  rw [value32, value62, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (200 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 62 = false ∨ valuation q 120 = false := by
  rw [value32, value62, value74, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (200 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 69 = false ∨ valuation q 75 = false := by
  rw [value32, value69, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (208 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 69 = false ∨ valuation q 76 = false := by
  rw [value32, value69, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (208 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 69 = false ∨ valuation q 120 = false := by
  rw [value32, value69, value74, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (208 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value32, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 75 = false ∨ valuation q 120 = false := by
  rw [value32, value74, value75, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 32 = false ∨ valuation q 76 = false ∨ valuation q 120 = false := by
  rw [value32, value74, value76, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 69 = false := by
  rw [value51, value62, value69, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (152 : Vertex) (200 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 75 = false := by
  rw [value51, value62, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (152 : Vertex) (200 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 76 = false := by
  rw [value51, value62, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (152 : Vertex) (200 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 120 = false := by
  rw [value51, value62, value74, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (152 : Vertex) (200 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 51 = false ∨ valuation q 69 = false ∨ valuation q 75 = false := by
  rw [value51, value69, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (152 : Vertex) (208 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 51 = false ∨ valuation q 69 = false ∨ valuation q 76 = false := by
  rw [value51, value69, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (152 : Vertex) (208 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 51 = false ∨ valuation q 69 = false ∨ valuation q 120 = false := by
  rw [value51, value69, value74, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (152 : Vertex) (208 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 51 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value51, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (152 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 51 = false ∨ valuation q 75 = false ∨ valuation q 120 = false := by
  rw [value51, value74, value75, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (152 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E089.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112089
