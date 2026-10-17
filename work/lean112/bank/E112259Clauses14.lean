import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 23 = false ∨ valuation q 60 = false ∨ valuation q 75 = false := by
  rw [value23, value60, value75, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (136 : Vertex) (160 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 23 = false ∨ valuation q 60 = false ∨ valuation q 82 = false := by
  rw [value23, value60, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (136 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 23 = false ∨ valuation q 60 = false ∨ valuation q 84 = false := by
  rw [value23, value60, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (136 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 23 = false ∨ valuation q 75 = false ∨ valuation q 82 = false := by
  rw [value23, value75, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (160 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 23 = false ∨ valuation q 75 = false ∨ valuation q 84 = false := by
  rw [value23, value75, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (160 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 23 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value23, value81, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (170 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 60 = false ∨ valuation q 75 = false ∨ valuation q 82 = false := by
  rw [value60, value75, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (136 : Vertex) (160 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 60 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value60, value81, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (136 : Vertex) (170 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 197 = true ∨ valuation q 60 = true ∨ valuation q 75 = true ∨ valuation q 82 = true ∨ valuation q 84 = true := by
  rw [value60, value75, value81, value82, value84, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(136 : Vertex), (160 : Vertex), (170 : Vertex), (172 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (40 : Vertex) [(136 : Vertex), (160 : Vertex), (170 : Vertex), (172 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 197 = true ∨ valuation q 23 = true ∨ valuation q 60 = true ∨ valuation q 75 = true ∨ valuation q 84 = true := by
  rw [value23, value60, value75, value81, value84, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(40 : Vertex), (136 : Vertex), (160 : Vertex), (172 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (170 : Vertex) [(40 : Vertex), (136 : Vertex), (160 : Vertex), (172 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 197 = true ∨ valuation q 23 = true ∨ valuation q 60 = true ∨ valuation q 75 = true ∨ valuation q 82 = true := by
  rw [value23, value60, value75, value81, value82, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(40 : Vertex), (136 : Vertex), (160 : Vertex), (170 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (172 : Vertex) [(40 : Vertex), (136 : Vertex), (160 : Vertex), (170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 24 = false ∨ valuation q 77 = false ∨ valuation q 93 = false := by
  rw [value24, value77, value82, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (42 : Vertex) (162 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 24 = false ∨ valuation q 81 = false ∨ valuation q 83 = false := by
  rw [value24, value81, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (42 : Vertex) (168 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 24 = false ∨ valuation q 81 = false ∨ valuation q 93 = false := by
  rw [value24, value81, value82, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (42 : Vertex) (168 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 24 = false ∨ valuation q 83 = false ∨ valuation q 93 = false := by
  rw [value24, value82, value83, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (42 : Vertex) (171 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 93 = false := by
  rw [value81, value82, value83, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (168 : Vertex) (171 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 198 = true ∨ valuation q 77 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 93 = true := by
  rw [value77, value81, value82, value83, value93, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(162 : Vertex), (168 : Vertex), (171 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (42 : Vertex) [(162 : Vertex), (168 : Vertex), (171 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 198 = true ∨ valuation q 24 = true ∨ valuation q 77 = true ∨ valuation q 83 = true ∨ valuation q 93 = true := by
  rw [value24, value77, value82, value83, value93, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(42 : Vertex), (162 : Vertex), (171 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (168 : Vertex) [(42 : Vertex), (162 : Vertex), (171 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 198 = true ∨ valuation q 24 = true ∨ valuation q 77 = true ∨ valuation q 81 = true ∨ valuation q 93 = true := by
  rw [value24, value77, value81, value82, value93, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(42 : Vertex), (162 : Vertex), (168 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (171 : Vertex) [(42 : Vertex), (162 : Vertex), (168 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 198 = true ∨ valuation q 24 = true ∨ valuation q 77 = true ∨ valuation q 81 = true ∨ valuation q 83 = true := by
  rw [value24, value77, value81, value82, value83, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(42 : Vertex), (162 : Vertex), (168 : Vertex), (171 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (186 : Vertex) [(42 : Vertex), (162 : Vertex), (168 : Vertex), (171 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 62 = false ∨ valuation q 78 = false ∨ valuation q 82 = false := by
  rw [value62, value78, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (139 : Vertex) (163 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 62 = false ∨ valuation q 78 = false ∨ valuation q 85 = false := by
  rw [value62, value78, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (139 : Vertex) (163 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 62 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value62, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (139 : Vertex) (170 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 78 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value78, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (163 : Vertex) (170 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 200 = true ∨ valuation q 81 = true := by
  rw [value81, value84, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (164 : Vertex) → w ∈ [(168 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (164 : Vertex) [(168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 200 = true ∨ valuation q 79 = true := by
  rw [value79, value84, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(164 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (168 : Vertex) [(164 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 26 = false ∨ valuation q 80 = false ∨ valuation q 83 = false := by
  rw [value26, value80, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (47 : Vertex) (167 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 201 = true ∨ valuation q 80 = true ∨ valuation q 83 = true := by
  rw [value80, value83, value85, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (47 : Vertex) → w ∈ [(167 : Vertex), (171 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (47 : Vertex) [(167 : Vertex), (171 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 201 = true ∨ valuation q 26 = true ∨ valuation q 83 = true := by
  rw [value26, value83, value85, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (167 : Vertex) → w ∈ [(47 : Vertex), (171 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (167 : Vertex) [(47 : Vertex), (171 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 27 = false ∨ valuation q 75 = false ∨ valuation q 87 = false := by
  rw [value27, value75, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (160 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 27 = false ∨ valuation q 75 = false ∨ valuation q 88 = false := by
  rw [value27, value75, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (160 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 27 = false ∨ valuation q 75 = false ∨ valuation q 89 = false := by
  rw [value27, value75, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (160 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E259.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112259
