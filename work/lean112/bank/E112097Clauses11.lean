import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 209 = true ∨ valuation q 17 = true ∨ valuation q 52 = true ∨ valuation q 88 = true ∨ valuation q 107 = true := by
  rw [value17, value52, value86, value88, value107, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(168 : Vertex), (296 : Vertex), (428 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (440 : Vertex) [(168 : Vertex), (296 : Vertex), (428 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 209 = true ∨ valuation q 17 = true ∨ valuation q 52 = true ∨ valuation q 88 = true ∨ valuation q 96 = true := by
  rw [value17, value52, value86, value88, value96, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(168 : Vertex), (296 : Vertex), (428 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (488 : Vertex) [(168 : Vertex), (296 : Vertex), (428 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 19 = false ∨ valuation q 83 = false ∨ valuation q 90 = false := by
  rw [value19, value83, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (419 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 210 = true ∨ valuation q 83 = true ∨ valuation q 90 = true ∨ valuation q 110 = true := by
  rw [value83, value87, value90, value110, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(419 : Vertex), (431 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (171 : Vertex) [(419 : Vertex), (431 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 210 = true ∨ valuation q 19 = true ∨ valuation q 90 = true ∨ valuation q 110 = true := by
  rw [value19, value87, value90, value110, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(171 : Vertex), (431 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (419 : Vertex) [(171 : Vertex), (431 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 210 = true ∨ valuation q 19 = true ∨ valuation q 83 = true ∨ valuation q 90 = true := by
  rw [value19, value83, value87, value90, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (491 : Vertex) → w ∈ [(171 : Vertex), (419 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (491 : Vertex) [(171 : Vertex), (419 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 86 = false := by
  rw [value20, value55, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (172 : Vertex) (300 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 89 = false := by
  rw [value20, value55, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (172 : Vertex) (300 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 97 = false := by
  rw [value20, value55, value88, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (172 : Vertex) (300 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 111 = false := by
  rw [value20, value55, value88, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (172 : Vertex) (300 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 20 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value20, value86, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (172 : Vertex) (424 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 20 = false ∨ valuation q 86 = false ∨ valuation q 97 = false := by
  rw [value20, value86, value88, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (172 : Vertex) (424 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 20 = false ∨ valuation q 86 = false ∨ valuation q 111 = false := by
  rw [value20, value86, value88, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (172 : Vertex) (424 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 20 = false ∨ valuation q 89 = false ∨ valuation q 97 = false := by
  rw [value20, value88, value89, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (172 : Vertex) (430 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 20 = false ∨ valuation q 89 = false ∨ valuation q 111 = false := by
  rw [value20, value88, value89, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (172 : Vertex) (430 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 20 = false ∨ valuation q 97 = false ∨ valuation q 111 = false := by
  rw [value20, value88, value97, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (172 : Vertex) (444 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 56 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value56, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (302 : Vertex) (428 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 112 = false := by
  rw [value88, value89, value90, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (428 : Vertex) (431 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 88 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value88, value89, value99, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (428 : Vertex) (446 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 212 = true ∨ valuation q 85 = true ∨ valuation q 88 = true ∨ valuation q 90 = true ∨ valuation q 99 = true ∨ valuation q 112 = true := by
  rw [value85, value88, value89, value90, value99, value112, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(422 : Vertex), (428 : Vertex), (431 : Vertex), (446 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (302 : Vertex) [(422 : Vertex), (428 : Vertex), (431 : Vertex), (446 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 212 = true ∨ valuation q 56 = true ∨ valuation q 88 = true ∨ valuation q 90 = true ∨ valuation q 99 = true ∨ valuation q 112 = true := by
  rw [value56, value88, value89, value90, value99, value112, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(302 : Vertex), (428 : Vertex), (431 : Vertex), (446 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (422 : Vertex) [(302 : Vertex), (428 : Vertex), (431 : Vertex), (446 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 212 = true ∨ valuation q 56 = true ∨ valuation q 85 = true ∨ valuation q 88 = true ∨ valuation q 99 = true ∨ valuation q 112 = true := by
  rw [value56, value85, value88, value89, value99, value112, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (431 : Vertex) → w ∈ [(302 : Vertex), (422 : Vertex), (428 : Vertex), (446 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (431 : Vertex) [(302 : Vertex), (422 : Vertex), (428 : Vertex), (446 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 100 = false := by
  rw [value87, value89, value90, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (427 : Vertex) (430 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 113 = false := by
  rw [value87, value89, value90, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (427 : Vertex) (430 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value87, value90, value100, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (427 : Vertex) (447 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 89 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value89, value90, value100, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (430 : Vertex) (447 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 213 = true ∨ valuation q 87 = true ∨ valuation q 89 = true ∨ valuation q 113 = true := by
  rw [value87, value89, value90, value113, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(427 : Vertex), (430 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (447 : Vertex) [(427 : Vertex), (430 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 96 = false := by
  rw [value91, value92, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (433 : Vertex) (434 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 214 = true ∨ valuation q 93 = true ∨ valuation q 96 = true := by
  rw [value91, value93, value96, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(434 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (433 : Vertex) [(434 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 214 = true ∨ valuation q 92 = true ∨ valuation q 96 = true := by
  rw [value91, value92, value96, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(433 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (434 : Vertex) [(433 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 214 = true ∨ valuation q 92 = true ∨ valuation q 93 = true := by
  rw [value91, value92, value93, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(433 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (440 : Vertex) [(433 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 21 = false ∨ valuation q 57 = false ∨ valuation q 82 = false := by
  rw [value21, value57, value82, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E097.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112097
