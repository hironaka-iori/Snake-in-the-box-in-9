import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 40 = false ∨ valuation q 49 = false := by
  rw [value13, value40, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (21 : Vertex) (133 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value13, value49, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (21 : Vertex) (148 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 40 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value40, value49, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (133 : Vertex) (148 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 41 = false ∨ valuation q 49 = false := by
  rw [value14, value41, value49, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (134 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 41 = false ∨ valuation q 52 = false := by
  rw [value14, value41, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (134 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 41 = false ∨ valuation q 55 = false := by
  rw [value14, value41, value51, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (134 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 41 = false ∨ valuation q 121 = false := by
  rw [value14, value41, value51, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (134 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value14, value49, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (148 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 49 = false ∨ valuation q 55 = false := by
  rw [value14, value49, value51, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (148 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 49 = false ∨ valuation q 121 = false := by
  rw [value14, value49, value51, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (148 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value14, value51, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (151 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 52 = false ∨ valuation q 121 = false := by
  rw [value14, value51, value52, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (151 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 55 = false ∨ valuation q 121 = false := by
  rw [value14, value51, value55, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (158 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 41 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value41, value49, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (134 : Vertex) (148 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 41 = false ∨ valuation q 49 = false ∨ valuation q 55 = false := by
  rw [value41, value49, value51, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (134 : Vertex) (148 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 41 = false ∨ valuation q 49 = false ∨ valuation q 121 = false := by
  rw [value41, value49, value51, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (134 : Vertex) (148 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 41 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value41, value51, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (134 : Vertex) (151 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 41 = false ∨ valuation q 55 = false ∨ valuation q 121 = false := by
  rw [value41, value51, value55, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (134 : Vertex) (158 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value49, value51, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (148 : Vertex) (151 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 121 = false := by
  rw [value49, value51, value52, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (148 : Vertex) (151 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 55 = false ∨ valuation q 121 = false := by
  rw [value49, value51, value55, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (148 : Vertex) (158 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 121 = false := by
  rw [value51, value52, value55, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (151 : Vertex) (158 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 15 = false ∨ valuation q 42 = false ∨ valuation q 122 = false := by
  rw [value15, value42, value52, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (23 : Vertex) (135 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 180 = true ∨ valuation q 15 = true ∨ valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 122 = true := by
  rw [value15, value50, value51, value52, value122, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(23 : Vertex), (149 : Vertex), (150 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (135 : Vertex) [(23 : Vertex), (149 : Vertex), (150 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 43 = true ∨ valuation q 48 = true ∨ valuation q 54 = true := by
  rw [value43, value48, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ∈ [(136 : Vertex), (144 : Vertex), (154 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (152 : Vertex) [(136 : Vertex), (144 : Vertex), (154 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 181 = true ∨ valuation q 48 = true ∨ valuation q 54 = true := by
  rw [value48, value53, value54, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(144 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (136 : Vertex) [(144 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 181 = true ∨ valuation q 43 = true ∨ valuation q 54 = true := by
  rw [value43, value53, value54, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(136 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (144 : Vertex) [(136 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 181 = true ∨ valuation q 43 = true ∨ valuation q 48 = true := by
  rw [value43, value48, value53, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(136 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (154 : Vertex) [(136 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 45 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value45, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (152 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 182 = true ∨ valuation q 45 = true ∨ valuation q 55 = true := by
  rw [value45, value54, value55, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (154 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(138 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (154 : Vertex) (152 : Vertex) [(138 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 183 = true ∨ valuation q 51 = true ∨ valuation q 65 = true ∨ valuation q 126 = true := by
  rw [value51, value55, value65, value126, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(150 : Vertex), (222 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (154 : Vertex) [(150 : Vertex), (222 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 183 = true ∨ valuation q 51 = true ∨ valuation q 54 = true ∨ valuation q 126 = true := by
  rw [value51, value54, value55, value126, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(150 : Vertex), (154 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (222 : Vertex) [(150 : Vertex), (154 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E055.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112055
