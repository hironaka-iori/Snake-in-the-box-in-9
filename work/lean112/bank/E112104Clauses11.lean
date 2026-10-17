import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 67 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value67, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 67 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value67, value102, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (488 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 67 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value67, value104, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (491 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 84 = false ∨ valuation q 97 = false ∨ valuation q 102 = false := by
  rw [value84, value97, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (426 : Vertex) (482 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 84 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value84, value97, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (426 : Vertex) (482 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 84 = false ∨ valuation q 97 = false ∨ valuation q 108 = false := by
  rw [value84, value97, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (426 : Vertex) (482 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 84 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value84, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (426 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 84 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value84, value102, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (426 : Vertex) (488 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 84 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value84, value104, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (426 : Vertex) (491 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 97 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value97, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (482 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 97 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value97, value104, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (482 : Vertex) (491 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value102, value104, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (488 : Vertex) (491 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 68 = false ∨ valuation q 85 = false ∨ valuation q 98 = false := by
  rw [value68, value85, value98, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (363 : Vertex) (427 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 68 = false ∨ valuation q 85 = false ∨ valuation q 103 = false := by
  rw [value68, value85, value103, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (363 : Vertex) (427 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 68 = false ∨ valuation q 85 = false ∨ valuation q 116 = false := by
  rw [value68, value85, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (363 : Vertex) (427 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 68 = false ∨ valuation q 98 = false ∨ valuation q 103 = false := by
  rw [value68, value98, value103, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (363 : Vertex) (483 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 68 = false ∨ valuation q 98 = false ∨ valuation q 116 = false := by
  rw [value68, value98, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (363 : Vertex) (483 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 68 = false ∨ valuation q 103 = false ∨ valuation q 104 = false := by
  rw [value68, value103, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (363 : Vertex) (489 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 68 = false ∨ valuation q 104 = false ∨ valuation q 116 = false := by
  rw [value68, value104, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (363 : Vertex) (490 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 85 = false ∨ valuation q 98 = false ∨ valuation q 103 = false := by
  rw [value85, value98, value103, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (427 : Vertex) (483 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 98 = false ∨ valuation q 103 = false ∨ valuation q 104 = false := by
  rw [value98, value103, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (483 : Vertex) (489 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 116 = false := by
  rw [value103, value104, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (489 : Vertex) (490 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 223 = true ∨ valuation q 68 = true ∨ valuation q 98 = true ∨ valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 116 = true := by
  rw [value68, value98, value103, value104, value105, value116, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(363 : Vertex), (483 : Vertex), (489 : Vertex), (490 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (427 : Vertex) [(363 : Vertex), (483 : Vertex), (489 : Vertex), (490 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 224 = false ∨ valuation q 106 = true := by
  rw [value106, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (492 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 69 = false ∨ valuation q 86 = false := by
  rw [value36, value69, value86, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (364 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 69 = false ∨ valuation q 99 = false := by
  rw [value36, value69, value99, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (364 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 69 = false ∨ valuation q 102 = false := by
  rw [value36, value69, value102, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (364 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 69 = false ∨ valuation q 107 = false := by
  rw [value36, value69, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (364 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 69 = false ∨ valuation q 108 = false := by
  rw [value36, value69, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (364 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 86 = false ∨ valuation q 99 = false := by
  rw [value36, value86, value99, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (428 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 86 = false ∨ valuation q 102 = false := by
  rw [value36, value86, value102, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (428 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 86 = false ∨ valuation q 107 = false := by
  rw [value36, value86, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (428 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E104.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112104
