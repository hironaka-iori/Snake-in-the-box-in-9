import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 43 = false := by
  rw [value19, value25, value30, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (54 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 60 = false := by
  rw [value19, value25, value30, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (54 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 86 = false := by
  rw [value19, value25, value30, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (54 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 31 = false := by
  rw [value19, value28, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (58 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 43 = false := by
  rw [value19, value28, value30, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (58 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 60 = false := by
  rw [value19, value28, value30, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (58 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 19 = false ∨ valuation q 31 = false ∨ valuation q 43 = false := by
  rw [value19, value30, value31, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (63 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 19 = false ∨ valuation q 31 = false ∨ valuation q 86 = false := by
  rw [value19, value30, value31, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (63 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 19 = false ∨ valuation q 43 = false ∨ valuation q 60 = false := by
  rw [value19, value30, value43, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (126 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 19 = false ∨ valuation q 43 = false ∨ valuation q 86 = false := by
  rw [value19, value30, value43, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (126 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 31 = false := by
  rw [value25, value28, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (54 : Vertex) (58 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 43 = false := by
  rw [value25, value28, value30, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (54 : Vertex) (58 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 25 = false ∨ valuation q 31 = false ∨ valuation q 43 = false := by
  rw [value25, value30, value31, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (54 : Vertex) (63 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 25 = false ∨ valuation q 43 = false ∨ valuation q 60 = false := by
  rw [value25, value30, value43, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (54 : Vertex) (126 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 25 = false ∨ valuation q 43 = false ∨ valuation q 86 = false := by
  rw [value25, value30, value43, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (54 : Vertex) (126 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 28 = false ∨ valuation q 31 = false ∨ valuation q 43 = false := by
  rw [value28, value30, value31, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (58 : Vertex) (63 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 28 = false ∨ valuation q 31 = false ∨ valuation q 60 = false := by
  rw [value28, value30, value31, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (58 : Vertex) (63 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 28 = false ∨ valuation q 31 = false ∨ valuation q 86 = false := by
  rw [value28, value30, value31, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (58 : Vertex) (63 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 28 = false ∨ valuation q 43 = false ∨ valuation q 86 = false := by
  rw [value28, value30, value43, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (58 : Vertex) (126 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 43 = false ∨ valuation q 60 = false := by
  rw [value30, value31, value43, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (63 : Vertex) (126 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 43 = false ∨ valuation q 86 = false := by
  rw [value30, value31, value43, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (63 : Vertex) (126 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 43 = false ∨ valuation q 60 = false ∨ valuation q 86 = false := by
  rw [value30, value43, value60, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (126 : Vertex) (190 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 26 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value26, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (63 : Vertex) (55 : Vertex) (59 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 157 = true ∨ valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 61 = true := by
  rw [value29, value30, value31, value61, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (63 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(59 : Vertex), (62 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (63 : Vertex) (55 : Vertex) [(59 : Vertex), (62 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 157 = true ∨ valuation q 26 = true ∨ valuation q 30 = true ∨ valuation q 61 = true := by
  rw [value26, value30, value31, value61, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (63 : Vertex) w → w ∈ region → w ≠ (59 : Vertex) → w ∈ [(55 : Vertex), (62 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (63 : Vertex) (59 : Vertex) [(55 : Vertex), (62 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 157 = true ∨ valuation q 26 = true ∨ valuation q 29 = true ∨ valuation q 61 = true := by
  rw [value26, value29, value31, value61, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (63 : Vertex) w → w ∈ region → w ≠ (62 : Vertex) → w ∈ [(55 : Vertex), (59 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (63 : Vertex) (62 : Vertex) [(55 : Vertex), (59 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 157 = true ∨ valuation q 26 = true ∨ valuation q 29 = true ∨ valuation q 30 = true := by
  rw [value26, value29, value30, value31, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (63 : Vertex) w → w ∈ region → w ≠ (191 : Vertex) → w ∈ [(55 : Vertex), (59 : Vertex), (62 : Vertex)] := by decide
  have hg := other_cover q (63 : Vertex) (191 : Vertex) [(55 : Vertex), (59 : Vertex), (62 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 158 = true := by
  rw [value32, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (66 : Vertex) (70 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 159 = true ∨ valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 35 = true := by
  rw [value32, value33, value34, value35, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(66 : Vertex), (78 : Vertex), (102 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (6 : Vertex) [(66 : Vertex), (78 : Vertex), (102 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 159 = true ∨ valuation q 3 = true ∨ valuation q 32 = true ∨ valuation q 34 = true := by
  rw [value3, value32, value33, value34, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (102 : Vertex) → w ∈ [(6 : Vertex), (66 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (102 : Vertex) [(6 : Vertex), (66 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 160 = true := by
  rw [value34, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (78 : Vertex) (70 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 161 = true ∨ valuation q 33 = true ∨ valuation q 39 = true := by
  rw [value33, value35, value39, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (102 : Vertex) w → w ∈ region → w ≠ (38 : Vertex) → w ∈ [(70 : Vertex), (118 : Vertex)] := by decide
  have hg := other_cover q (102 : Vertex) (38 : Vertex) [(70 : Vertex), (118 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block11 (q : Snake 81) (h : Conditions q) : B112E121.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112121
