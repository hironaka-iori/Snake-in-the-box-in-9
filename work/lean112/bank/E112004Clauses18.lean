import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 93 = false := by
  rw [value85, value87, value88, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (420 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 207 = true ∨ valuation q 88 = true ∨ valuation q 93 = true := by
  rw [value87, value88, value93, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(423 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (420 : Vertex) [(423 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 207 = true ∨ valuation q 85 = true ∨ valuation q 93 = true := by
  rw [value85, value87, value93, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(420 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (423 : Vertex) [(420 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 207 = true ∨ valuation q 85 = true ∨ valuation q 88 = true := by
  rw [value85, value87, value88, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(420 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (430 : Vertex) [(420 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 38 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value38, value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 38 = false ∨ valuation q 86 = false ∨ valuation q 97 = false := by
  rw [value38, value86, value88, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (421 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 38 = false ∨ valuation q 86 = false ∨ valuation q 108 = false := by
  rw [value38, value86, value88, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (421 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 38 = false ∨ valuation q 87 = false ∨ valuation q 97 = false := by
  rw [value38, value87, value88, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (422 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 38 = false ∨ valuation q 87 = false ∨ valuation q 108 = false := by
  rw [value38, value87, value88, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (422 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 38 = false ∨ valuation q 97 = false ∨ valuation q 108 = false := by
  rw [value38, value88, value97, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (439 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 97 = false := by
  rw [value86, value87, value88, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (422 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 108 = false := by
  rw [value86, value87, value88, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (422 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 97 = false ∨ valuation q 108 = false := by
  rw [value86, value88, value97, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (439 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 87 = false ∨ valuation q 97 = false ∨ valuation q 108 = false := by
  rw [value87, value88, value97, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (422 : Vertex) (439 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 84 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value84, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (425 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 84 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value84, value89, value90, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (425 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 84 = false ∨ valuation q 90 = false ∨ valuation q 109 = false := by
  rw [value84, value89, value90, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (425 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 84 = false ∨ valuation q 91 = false ∨ valuation q 98 = false := by
  rw [value84, value89, value91, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (426 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 84 = false ∨ valuation q 91 = false ∨ valuation q 109 = false := by
  rw [value84, value89, value91, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (426 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 84 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value84, value89, value98, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 98 = false := by
  rw [value89, value90, value91, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (425 : Vertex) (426 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 109 = false := by
  rw [value89, value90, value91, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (425 : Vertex) (426 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value89, value90, value98, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (425 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value89, value91, value98, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (426 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 39 = false ∨ valuation q 89 = false ∨ valuation q 92 = false := by
  rw [value39, value89, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (169 : Vertex) (424 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 39 = false ∨ valuation q 92 = false ∨ valuation q 99 = false := by
  rw [value39, value90, value92, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (169 : Vertex) (427 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 210 = true ∨ valuation q 89 = true ∨ valuation q 92 = true ∨ valuation q 99 = true := by
  rw [value89, value90, value92, value99, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(424 : Vertex), (427 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (169 : Vertex) [(424 : Vertex), (427 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 210 = true ∨ valuation q 39 = true ∨ valuation q 92 = true ∨ valuation q 99 = true := by
  rw [value39, value90, value92, value99, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(169 : Vertex), (427 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (424 : Vertex) [(169 : Vertex), (427 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 210 = true ∨ valuation q 39 = true ∨ valuation q 89 = true ∨ valuation q 99 = true := by
  rw [value39, value89, value90, value99, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(169 : Vertex), (424 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (427 : Vertex) [(169 : Vertex), (424 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 210 = true ∨ valuation q 39 = true ∨ valuation q 89 = true ∨ valuation q 92 = true := by
  rw [value39, value89, value90, value92, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(169 : Vertex), (424 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (441 : Vertex) [(169 : Vertex), (424 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 89 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value89, value91, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (424 : Vertex) (427 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 89 = false ∨ valuation q 93 = false ∨ valuation q 100 = false := by
  rw [value89, value91, value93, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (424 : Vertex) (430 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E004.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112004
