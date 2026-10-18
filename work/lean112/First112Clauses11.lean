import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 22 = false ∨ valuation q 58 = false ∨ valuation q 82 = false := by
  rw [value22, value58, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 22 = false ∨ valuation q 58 = false ∨ valuation q 83 = false := by
  rw [value22, value58, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 22 = false ∨ valuation q 58 = false ∨ valuation q 86 = false := by
  rw [value22, value58, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 22 = false ∨ valuation q 58 = false ∨ valuation q 91 = false := by
  rw [value22, value58, value85, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 22 = false ∨ valuation q 58 = false ∨ valuation q 108 = false := by
  rw [value22, value58, value85, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 22 = false ∨ valuation q 91 = false ∨ valuation q 108 = false := by
  rw [value22, value85, value91, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 58 = false ∨ valuation q 83 = false ∨ valuation q 108 = false := by
  rw [value58, value83, value85, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (420 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 58 = false ∨ valuation q 86 = false ∨ valuation q 108 = false := by
  rw [value58, value85, value86, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (423 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 58 = false ∨ valuation q 91 = false ∨ valuation q 108 = false := by
  rw [value58, value85, value91, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 108 = false := by
  rw [value82, value83, value85, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (418 : Vertex) (420 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 91 = false := by
  rw [value83, value85, value86, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (420 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 108 = false := by
  rw [value83, value85, value86, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (420 : Vertex) (423 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 207 = true ∨ valuation q 58 = true ∨ valuation q 82 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 91 = true ∨ valuation q 108 = true := by
  rw [value58, value82, value83, value85, value86, value91, value108, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(294 : Vertex), (418 : Vertex), (420 : Vertex), (423 : Vertex), (430 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (166 : Vertex) [(294 : Vertex), (418 : Vertex), (420 : Vertex), (423 : Vertex), (430 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 207 = true ∨ valuation q 22 = true ∨ valuation q 58 = true ∨ valuation q 82 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 91 = true := by
  rw [value22, value58, value82, value83, value85, value86, value91, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(166 : Vertex), (294 : Vertex), (418 : Vertex), (420 : Vertex), (423 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (486 : Vertex) [(166 : Vertex), (294 : Vertex), (418 : Vertex), (420 : Vertex), (423 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 23 = false ∨ valuation q 59 = false ∨ valuation q 92 = false := by
  rw [value23, value59, value86, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (295 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 23 = false ∨ valuation q 59 = false ∨ valuation q 97 = false := by
  rw [value23, value59, value86, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (295 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 23 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value23, value84, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 23 = false ∨ valuation q 84 = false ∨ valuation q 92 = false := by
  rw [value23, value84, value86, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (421 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 23 = false ∨ valuation q 84 = false ∨ valuation q 97 = false := by
  rw [value23, value84, value86, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (421 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 23 = false ∨ valuation q 85 = false ∨ valuation q 97 = false := by
  rw [value23, value85, value86, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (422 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 23 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value23, value86, value92, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (431 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 59 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value59, value84, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 59 = false ∨ valuation q 84 = false ∨ valuation q 97 = false := by
  rw [value59, value84, value86, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (421 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 59 = false ∨ valuation q 85 = false ∨ valuation q 97 = false := by
  rw [value59, value85, value86, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (422 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 59 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value59, value86, value92, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (431 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 92 = false := by
  rw [value84, value85, value86, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (422 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 97 = false := by
  rw [value84, value85, value86, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (422 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 84 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value84, value86, value92, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (431 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 85 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value85, value86, value92, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (422 : Vertex) (431 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 87 = true := by
  rw [value87, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (424 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 24 = false ∨ valuation q 60 = false ∨ valuation q 80 = false := by
  rw [value24, value60, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 24 = false ∨ valuation q 60 = false ∨ valuation q 88 = false := by
  rw [value24, value60, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.First112
