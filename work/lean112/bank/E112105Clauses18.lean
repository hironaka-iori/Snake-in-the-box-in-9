import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 47 = false ∨ valuation q 84 = false ∨ valuation q 103 = false := by
  rw [value47, value84, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (384 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 47 = false ∨ valuation q 84 = false ∨ valuation q 114 = false := by
  rw [value47, value84, value102, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (384 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 47 = false ∨ valuation q 103 = false ∨ valuation q 114 = false := by
  rw [value47, value102, value103, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (449 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 67 = false ∨ valuation q 84 = false ∨ valuation q 103 = false := by
  rw [value67, value84, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (320 : Vertex) (384 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 67 = false ∨ valuation q 84 = false ∨ valuation q 104 = false := by
  rw [value67, value84, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (320 : Vertex) (384 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 67 = false ∨ valuation q 84 = false ∨ valuation q 114 = false := by
  rw [value67, value84, value102, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (320 : Vertex) (384 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 67 = false ∨ valuation q 103 = false ∨ valuation q 104 = false := by
  rw [value67, value102, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (320 : Vertex) (449 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 67 = false ∨ valuation q 103 = false ∨ valuation q 114 = false := by
  rw [value67, value102, value103, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (320 : Vertex) (449 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 67 = false ∨ valuation q 104 = false ∨ valuation q 114 = false := by
  rw [value67, value102, value104, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (320 : Vertex) (450 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 84 = false ∨ valuation q 103 = false ∨ valuation q 104 = false := by
  rw [value84, value102, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (384 : Vertex) (449 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 84 = false ∨ valuation q 103 = false ∨ valuation q 114 = false := by
  rw [value84, value102, value103, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (384 : Vertex) (449 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 84 = false ∨ valuation q 104 = false ∨ valuation q 114 = false := by
  rw [value84, value102, value104, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (384 : Vertex) (450 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 114 = false := by
  rw [value102, value103, value104, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (449 : Vertex) (450 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 226 = true ∨ valuation q 47 = true ∨ valuation q 84 = true ∨ valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 114 = true := by
  rw [value47, value84, value102, value103, value104, value114, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(192 : Vertex), (384 : Vertex), (449 : Vertex), (450 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (320 : Vertex) [(192 : Vertex), (384 : Vertex), (449 : Vertex), (450 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 226 = true ∨ valuation q 47 = true ∨ valuation q 67 = true ∨ valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 114 = true := by
  rw [value47, value67, value102, value103, value104, value114, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(192 : Vertex), (320 : Vertex), (449 : Vertex), (450 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (384 : Vertex) [(192 : Vertex), (320 : Vertex), (449 : Vertex), (450 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value102, value103, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value102, value103, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (451 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 115 = false := by
  rw [value102, value103, value105, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (451 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 102 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value102, value103, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (453 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 102 = false ∨ valuation q 106 = false ∨ valuation q 115 = false := by
  rw [value102, value103, value106, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 102 = false ∨ valuation q 108 = false ∨ valuation q 115 = false := by
  rw [value102, value103, value108, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (457 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value103, value105, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (451 : Vertex) (453 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 115 = false := by
  rw [value103, value105, value106, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (451 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 115 = false := by
  rw [value103, value105, value108, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (451 : Vertex) (457 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 115 = false := by
  rw [value103, value106, value108, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (453 : Vertex) (457 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 227 = true ∨ valuation q 102 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 115 = true := by
  rw [value102, value103, value106, value108, value115, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(448 : Vertex), (453 : Vertex), (457 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (451 : Vertex) [(448 : Vertex), (453 : Vertex), (457 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 227 = true ∨ valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 108 = true ∨ valuation q 115 = true := by
  rw [value102, value103, value105, value108, value115, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(448 : Vertex), (451 : Vertex), (457 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (453 : Vertex) [(448 : Vertex), (451 : Vertex), (457 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 227 = true ∨ valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 115 = true := by
  rw [value102, value103, value105, value106, value115, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(448 : Vertex), (451 : Vertex), (453 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (457 : Vertex) [(448 : Vertex), (451 : Vertex), (453 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 227 = true ∨ valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 108 = true := by
  rw [value102, value103, value105, value106, value108, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (465 : Vertex) → w ∈ [(448 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (465 : Vertex) [(448 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 68 = false ∨ valuation q 85 = false := by
  rw [value48, value68, value85, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 68 = false ∨ valuation q 102 = false := by
  rw [value48, value68, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (322 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 68 = false ∨ valuation q 105 = false := by
  rw [value48, value68, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (322 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E105.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112105
