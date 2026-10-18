import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 51 = false ∨ valuation q 97 = false := by
  rw [value16, value51, value85, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (293 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value16, value82, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (417 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value16, value84, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 51 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value51, value84, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (293 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 82 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value82, value84, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 206 = true ∨ valuation q 51 = true ∨ valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 87 = true ∨ valuation q 97 = true := by
  rw [value51, value82, value84, value85, value87, value97, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(293 : Vertex), (417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (165 : Vertex) [(293 : Vertex), (417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 206 = true ∨ valuation q 16 = true ∨ valuation q 51 = true ∨ valuation q 82 = true ∨ valuation q 87 = true ∨ valuation q 97 = true := by
  rw [value16, value51, value82, value85, value87, value97, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(165 : Vertex), (293 : Vertex), (417 : Vertex), (423 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (420 : Vertex) [(165 : Vertex), (293 : Vertex), (417 : Vertex), (423 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 206 = true ∨ valuation q 16 = true ∨ valuation q 51 = true ∨ valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 97 = true := by
  rw [value16, value51, value82, value84, value85, value97, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(165 : Vertex), (293 : Vertex), (417 : Vertex), (420 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (423 : Vertex) [(165 : Vertex), (293 : Vertex), (417 : Vertex), (420 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 206 = true ∨ valuation q 16 = true ∨ valuation q 51 = true ∨ valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 87 = true := by
  rw [value16, value51, value82, value84, value85, value87, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(165 : Vertex), (293 : Vertex), (417 : Vertex), (420 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (437 : Vertex) [(165 : Vertex), (293 : Vertex), (417 : Vertex), (420 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 84 = false := by
  rw [value17, value52, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 87 = false := by
  rw [value17, value52, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 92 = false := by
  rw [value17, value52, value86, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 106 = false := by
  rw [value17, value52, value86, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 17 = false ∨ valuation q 83 = false ∨ valuation q 106 = false := by
  rw [value17, value83, value86, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (418 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 17 = false ∨ valuation q 87 = false ∨ valuation q 92 = false := by
  rw [value17, value86, value87, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 17 = false ∨ valuation q 87 = false ∨ valuation q 106 = false := by
  rw [value17, value86, value87, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (423 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 17 = false ∨ valuation q 92 = false ∨ valuation q 106 = false := by
  rw [value17, value86, value92, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 52 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value52, value84, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 52 = false ∨ valuation q 84 = false ∨ valuation q 106 = false := by
  rw [value52, value84, value86, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (420 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 52 = false ∨ valuation q 87 = false ∨ valuation q 92 = false := by
  rw [value52, value86, value87, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 52 = false ∨ valuation q 87 = false ∨ valuation q 106 = false := by
  rw [value52, value86, value87, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (423 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 52 = false ∨ valuation q 92 = false ∨ valuation q 106 = false := by
  rw [value52, value86, value92, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 53 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value53, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 53 = false ∨ valuation q 85 = false ∨ valuation q 93 = false := by
  rw [value53, value85, value87, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (421 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 53 = false ∨ valuation q 85 = false ∨ valuation q 98 = false := by
  rw [value53, value85, value87, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (421 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 53 = false ∨ valuation q 85 = false ∨ valuation q 107 = false := by
  rw [value53, value85, value87, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (421 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 53 = false ∨ valuation q 86 = false ∨ valuation q 93 = false := by
  rw [value53, value86, value87, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (422 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 53 = false ∨ valuation q 86 = false ∨ valuation q 98 = false := by
  rw [value53, value86, value87, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (422 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 53 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value53, value87, value93, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (431 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 53 = false ∨ valuation q 93 = false ∨ valuation q 107 = false := by
  rw [value53, value87, value93, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (431 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 53 = false ∨ valuation q 98 = false ∨ valuation q 107 = false := by
  rw [value53, value87, value98, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (439 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 93 = false := by
  rw [value85, value86, value87, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (422 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E024.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112024
