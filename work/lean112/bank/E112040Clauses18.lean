import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 223 = true ∨ valuation q 32 = true ∨ valuation q 85 = true ∨ valuation q 109 = true := by
  rw [value32, value85, value103, value109, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (371 : Vertex) w → w ∈ region → w ≠ (375 : Vertex) → w ∈ [(115 : Vertex), (307 : Vertex), (379 : Vertex)] := by decide
  have hg := other_cover q (371 : Vertex) (375 : Vertex) [(115 : Vertex), (307 : Vertex), (379 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 94 = false ∨ valuation q 105 = false ∨ valuation q 110 = false := by
  rw [value94, value104, value105, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (357 : Vertex) (375 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 224 = true ∨ valuation q 105 = true ∨ valuation q 110 = true := by
  rw [value104, value105, value110, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (357 : Vertex) → w ∈ [(375 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (357 : Vertex) [(375 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 225 = true ∨ valuation q 35 = true ∨ valuation q 96 = true ∨ valuation q 104 = true := by
  rw [value35, value96, value104, value105, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (371 : Vertex) → w ∈ [(119 : Vertex), (359 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (371 : Vertex) [(119 : Vertex), (359 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 225 = true ∨ valuation q 35 = true ∨ valuation q 96 = true ∨ valuation q 103 = true := by
  rw [value35, value96, value103, value105, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(119 : Vertex), (359 : Vertex), (371 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (373 : Vertex) [(119 : Vertex), (359 : Vertex), (371 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 97 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value97, value102, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (360 : Vertex) (368 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 97 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value97, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (360 : Vertex) (377 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 102 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value102, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (368 : Vertex) (377 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 226 = true ∨ valuation q 97 = true ∨ valuation q 102 = true ∨ valuation q 107 = true ∨ valuation q 108 = true := by
  rw [value97, value102, value106, value107, value108, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(360 : Vertex), (368 : Vertex), (377 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (120 : Vertex) [(360 : Vertex), (368 : Vertex), (377 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 226 = true ∨ valuation q 36 = true ∨ valuation q 102 = true ∨ valuation q 107 = true ∨ valuation q 108 = true := by
  rw [value36, value102, value106, value107, value108, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(120 : Vertex), (368 : Vertex), (377 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (360 : Vertex) [(120 : Vertex), (368 : Vertex), (377 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 226 = true ∨ valuation q 36 = true ∨ valuation q 97 = true ∨ valuation q 107 = true ∨ valuation q 108 = true := by
  rw [value36, value97, value106, value107, value108, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(120 : Vertex), (360 : Vertex), (377 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (368 : Vertex) [(120 : Vertex), (360 : Vertex), (377 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 226 = true ∨ valuation q 36 = true ∨ valuation q 97 = true ∨ valuation q 102 = true ∨ valuation q 108 = true := by
  rw [value36, value97, value102, value106, value108, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(120 : Vertex), (360 : Vertex), (368 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (377 : Vertex) [(120 : Vertex), (360 : Vertex), (368 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 226 = true ∨ valuation q 36 = true ∨ valuation q 97 = true ∨ valuation q 102 = true ∨ valuation q 107 = true := by
  rw [value36, value97, value102, value106, value107, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(120 : Vertex), (360 : Vertex), (368 : Vertex), (377 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (378 : Vertex) [(120 : Vertex), (360 : Vertex), (368 : Vertex), (377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 37 = false ∨ valuation q 98 = false ∨ valuation q 106 = false := by
  rw [value37, value98, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (377 : Vertex) (121 : Vertex) (361 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 37 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value37, value98, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (377 : Vertex) (121 : Vertex) (361 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 37 = false ∨ valuation q 98 = false ∨ valuation q 110 = false := by
  rw [value37, value98, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (377 : Vertex) (121 : Vertex) (361 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 37 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value37, value106, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (377 : Vertex) (121 : Vertex) (376 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 37 = false ∨ valuation q 106 = false ∨ valuation q 110 = false := by
  rw [value37, value106, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (377 : Vertex) (121 : Vertex) (376 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 37 = false ∨ valuation q 109 = false ∨ valuation q 110 = false := by
  rw [value37, value107, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (377 : Vertex) (121 : Vertex) (379 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 98 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value98, value106, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (377 : Vertex) (361 : Vertex) (376 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 98 = false ∨ valuation q 106 = false ∨ valuation q 110 = false := by
  rw [value98, value106, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (377 : Vertex) (361 : Vertex) (376 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 98 = false ∨ valuation q 109 = false ∨ valuation q 110 = false := by
  rw [value98, value107, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (377 : Vertex) (361 : Vertex) (379 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 106 = false ∨ valuation q 109 = false ∨ valuation q 110 = false := by
  rw [value106, value107, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (377 : Vertex) (376 : Vertex) (379 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 227 = true ∨ valuation q 37 = true ∨ valuation q 106 = true ∨ valuation q 109 = true ∨ valuation q 110 = true := by
  rw [value37, value106, value107, value109, value110, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (377 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(121 : Vertex), (376 : Vertex), (379 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (377 : Vertex) (361 : Vertex) [(121 : Vertex), (376 : Vertex), (379 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 38 = false ∨ valuation q 88 = false ∨ valuation q 99 = false := by
  rw [value38, value88, value99, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (314 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 38 = false ∨ valuation q 88 = false ∨ valuation q 106 = false := by
  rw [value38, value88, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (314 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 38 = false ∨ valuation q 88 = false ∨ valuation q 109 = false := by
  rw [value38, value88, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (314 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 38 = false ∨ valuation q 88 = false ∨ valuation q 111 = false := by
  rw [value38, value88, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (314 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 38 = false ∨ valuation q 99 = false ∨ valuation q 106 = false := by
  rw [value38, value99, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (362 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 38 = false ∨ valuation q 99 = false ∨ valuation q 109 = false := by
  rw [value38, value99, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 38 = false ∨ valuation q 99 = false ∨ valuation q 111 = false := by
  rw [value38, value99, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (362 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 38 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value38, value106, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (376 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E040.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112040
