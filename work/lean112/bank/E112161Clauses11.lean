import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 196 = true ∨ valuation q 18 = true ∨ valuation q 52 = true ∨ valuation q 84 = true := by
  rw [value18, value52, value84, value85, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(139 : Vertex), (267 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (411 : Vertex) [(139 : Vertex), (267 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 81 = false ∨ valuation q 87 = false ∨ valuation q 93 = false := by
  rw [value81, value86, value87, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 197 = true ∨ valuation q 81 = true ∨ valuation q 93 = true := by
  rw [value81, value86, value93, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(388 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (397 : Vertex) [(388 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 197 = true ∨ valuation q 81 = true ∨ valuation q 87 = true := by
  rw [value81, value86, value87, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(388 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (412 : Vertex) [(388 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 87 = true := by
  rw [value87, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (397 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 82 = true ∨ valuation q 86 = true := by
  rw [value82, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ∈ [(389 : Vertex), (396 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (397 : Vertex) [(389 : Vertex), (396 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 198 = true ∨ valuation q 86 = true := by
  rw [value86, value87, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(396 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (389 : Vertex) [(396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 198 = true ∨ valuation q 82 = true := by
  rw [value82, value87, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(389 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (396 : Vertex) [(389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 88 = true := by
  rw [value88, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (400 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 20 = true ∨ valuation q 79 = true ∨ valuation q 89 = true := by
  rw [value20, value79, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ∈ [(144 : Vertex), (384 : Vertex), (401 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (400 : Vertex) [(144 : Vertex), (384 : Vertex), (401 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 199 = true ∨ valuation q 79 = true ∨ valuation q 89 = true := by
  rw [value79, value88, value89, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(384 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (400 : Vertex) (144 : Vertex) [(384 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 199 = true ∨ valuation q 20 = true ∨ valuation q 89 = true := by
  rw [value20, value88, value89, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(144 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (400 : Vertex) (384 : Vertex) [(144 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 199 = true ∨ valuation q 20 = true ∨ valuation q 79 = true := by
  rw [value20, value79, value88, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(144 : Vertex), (384 : Vertex)] := by decide
  have hg := other_cover q (400 : Vertex) (401 : Vertex) [(144 : Vertex), (384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 200 = true ∨ valuation q 90 = true := by
  rw [value89, value90, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(403 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (400 : Vertex) [(403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 200 = true ∨ valuation q 88 = true := by
  rw [value88, value89, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(400 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (403 : Vertex) [(400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 90 = true := by
  rw [value90, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (403 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 89 = true ∨ valuation q 91 = true ∨ valuation q 92 = true := by
  rw [value89, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ∈ [(401 : Vertex), (407 : Vertex), (411 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (403 : Vertex) [(401 : Vertex), (407 : Vertex), (411 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 201 = true ∨ valuation q 91 = true ∨ valuation q 92 = true := by
  rw [value90, value91, value92, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(407 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (401 : Vertex) [(407 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 201 = true ∨ valuation q 89 = true ∨ valuation q 92 = true := by
  rw [value89, value90, value92, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(401 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (407 : Vertex) [(401 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 201 = true ∨ valuation q 89 = true ∨ valuation q 91 = true := by
  rw [value89, value90, value91, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(401 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (411 : Vertex) [(401 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 24 = false ∨ valuation q 57 = false ∨ valuation q 90 = false := by
  rw [value24, value57, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 24 = false ∨ valuation q 57 = false ∨ valuation q 95 = false := by
  rw [value24, value57, value91, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 24 = false ∨ valuation q 90 = false ∨ valuation q 95 = false := by
  rw [value24, value90, value91, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (403 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 57 = false ∨ valuation q 90 = false ∨ valuation q 95 = false := by
  rw [value57, value90, value91, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (403 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 85 = false ∨ valuation q 90 = false ∨ valuation q 95 = false := by
  rw [value85, value90, value92, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (395 : Vertex) (403 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 203 = true ∨ valuation q 85 = true ∨ valuation q 90 = true := by
  rw [value85, value90, value92, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(395 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (415 : Vertex) [(395 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 93 = true := by
  rw [value93, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (412 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 204 = true ∨ valuation q 94 = true := by
  rw [value93, value94, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (396 : Vertex) [(414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 204 = true ∨ valuation q 86 = true := by
  rw [value86, value93, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(396 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (414 : Vertex) [(396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 205 = true ∨ valuation q 95 = true := by
  rw [value94, value95, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(415 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (412 : Vertex) [(415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 205 = true ∨ valuation q 93 = true := by
  rw [value93, value94, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(412 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (415 : Vertex) [(412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 206 = true ∨ valuation q 92 = true ∨ valuation q 94 = true := by
  rw [value92, value94, value95, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(411 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (407 : Vertex) [(411 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block11 (q : Snake 81) (h : Conditions q) : B112E161.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112161
