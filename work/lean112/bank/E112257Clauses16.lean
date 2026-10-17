import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 217 = true ∨ valuation q 100 = true ∨ valuation q 103 = true := by
  rw [value100, value101, value103, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(398 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (271 : Vertex) [(398 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 217 = true ∨ valuation q 84 = true ∨ valuation q 100 = true := by
  rw [value84, value100, value101, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(271 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (415 : Vertex) [(271 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 218 = true ∨ valuation q 103 = true := by
  rw [value102, value103, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(415 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (279 : Vertex) [(415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 218 = true ∨ valuation q 86 = true := by
  rw [value86, value102, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(279 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (415 : Vertex) [(279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 219 = true ∨ valuation q 102 = true := by
  rw [value102, value103, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(407 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (399 : Vertex) [(407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 219 = true ∨ valuation q 101 = true := by
  rw [value101, value103, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(399 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (407 : Vertex) [(399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 107 = false ∨ valuation q 111 = false := by
  rw [value104, value105, value107, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (423 : Vertex) (427 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 220 = true ∨ valuation q 107 = true ∨ valuation q 111 = true := by
  rw [value104, value107, value111, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (423 : Vertex) [(427 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 220 = true ∨ valuation q 105 = true ∨ valuation q 111 = true := by
  rw [value104, value105, value111, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(423 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (427 : Vertex) [(423 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 220 = true ∨ valuation q 105 = true ∨ valuation q 107 = true := by
  rw [value104, value105, value107, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(423 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (435 : Vertex) [(423 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 221 = true ∨ valuation q 104 = true := by
  rw [value104, value105, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (423 : Vertex) w → w ∈ region → w ≠ (295 : Vertex) → w ∈ [(419 : Vertex)] := by decide
  have hg := other_cover q (423 : Vertex) (295 : Vertex) [(419 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 221 = true ∨ valuation q 88 = true := by
  rw [value88, value105, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (423 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(295 : Vertex)] := by decide
  have hg := other_cover q (423 : Vertex) (419 : Vertex) [(295 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 90 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value90, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (419 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 90 = false ∨ valuation q 104 = false ∨ valuation q 115 = false := by
  rw [value90, value104, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (419 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 90 = false ∨ valuation q 106 = false ∨ valuation q 115 = false := by
  rw [value90, value106, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 223 = true ∨ valuation q 90 = true ∨ valuation q 106 = true ∨ valuation q 115 = true := by
  rw [value90, value106, value107, value115, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(299 : Vertex), (426 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (419 : Vertex) [(299 : Vertex), (426 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 224 = true := by
  rw [value108, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (429 : Vertex) (173 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 92 = false ∨ valuation q 100 = false ∨ valuation q 116 = false := by
  rw [value92, value100, value109, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (302 : Vertex) (398 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 92 = false ∨ valuation q 106 = false ∨ valuation q 116 = false := by
  rw [value92, value106, value109, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (302 : Vertex) (426 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 100 = false ∨ valuation q 106 = false ∨ valuation q 116 = false := by
  rw [value100, value106, value109, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (398 : Vertex) (426 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 225 = true ∨ valuation q 92 = true ∨ valuation q 100 = true ∨ valuation q 106 = true := by
  rw [value92, value100, value106, value109, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(302 : Vertex), (398 : Vertex), (426 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (446 : Vertex) [(302 : Vertex), (398 : Vertex), (426 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 93 = false ∨ valuation q 111 = false ∨ valuation q 114 = false := by
  rw [value93, value110, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (435 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 226 = true ∨ valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 114 = true := by
  rw [value110, value111, value112, value114, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(435 : Vertex), (437 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (305 : Vertex) [(435 : Vertex), (437 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 226 = true ∨ valuation q 93 = true ∨ valuation q 112 = true ∨ valuation q 114 = true := by
  rw [value93, value110, value112, value114, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(305 : Vertex), (437 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (435 : Vertex) [(305 : Vertex), (437 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 226 = true ∨ valuation q 93 = true ∨ valuation q 111 = true ∨ valuation q 112 = true := by
  rw [value93, value110, value111, value112, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(305 : Vertex), (435 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (441 : Vertex) [(305 : Vertex), (435 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 69 = false ∨ valuation q 94 = false ∨ valuation q 104 = false := by
  rw [value69, value94, value104, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 94 = false ∨ valuation q 104 = false ∨ valuation q 110 = false := by
  rw [value94, value104, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (419 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 94 = false ∨ valuation q 104 = false ∨ valuation q 115 = false := by
  rw [value94, value104, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (419 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 94 = false ∨ valuation q 110 = false ∨ valuation q 115 = false := by
  rw [value94, value110, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 104 = false ∨ valuation q 110 = false ∨ valuation q 115 = false := by
  rw [value104, value110, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (419 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 227 = true ∨ valuation q 69 = true ∨ valuation q 94 = true ∨ valuation q 110 = true ∨ valuation q 115 = true := by
  rw [value69, value94, value110, value111, value115, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(179 : Vertex), (307 : Vertex), (433 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (419 : Vertex) [(179 : Vertex), (307 : Vertex), (433 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 228 = true := by
  rw [value112, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (437 : Vertex) (433 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block16 (q : Snake 81) (h : Conditions q) : B112E257.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112257
