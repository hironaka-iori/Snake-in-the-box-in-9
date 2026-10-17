import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 108 = true := by
  rw [value108, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (464 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = true ∨ valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 114 = true := by
  rw [value96, value108, value109, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ∈ [(448 : Vertex), (466 : Vertex), (468 : Vertex), (472 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (464 : Vertex) [(448 : Vertex), (466 : Vertex), (468 : Vertex), (472 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value96, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 109 = false ∨ valuation q 114 = false := by
  rw [value96, value108, value109, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 111 = false ∨ valuation q 114 = false := by
  rw [value96, value108, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 114 = false := by
  rw [value108, value109, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (466 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 226 = true ∨ valuation q 96 = true ∨ valuation q 109 = true ∨ valuation q 111 = true := by
  rw [value96, value108, value109, value111, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(448 : Vertex), (466 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (472 : Vertex) [(448 : Vertex), (466 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 98 = false ∨ valuation q 108 = false ∨ valuation q 112 = false := by
  rw [value98, value108, value109, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (450 : Vertex) (464 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 98 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value98, value109, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (450 : Vertex) (467 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 112 = true := by
  rw [value108, value109, value110, value112, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(464 : Vertex), (467 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (450 : Vertex) [(464 : Vertex), (467 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 98 = true ∨ valuation q 110 = true ∨ valuation q 112 = true := by
  rw [value98, value109, value110, value112, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(450 : Vertex), (467 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (464 : Vertex) [(450 : Vertex), (467 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 98 = true ∨ valuation q 108 = true ∨ valuation q 112 = true := by
  rw [value98, value108, value109, value112, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(450 : Vertex), (464 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (467 : Vertex) [(450 : Vertex), (464 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 98 = true ∨ valuation q 108 = true ∨ valuation q 110 = true := by
  rw [value98, value108, value109, value110, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(450 : Vertex), (464 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (470 : Vertex) [(450 : Vertex), (464 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 88 = false ∨ valuation q 99 = false ∨ valuation q 109 = false := by
  rw [value88, value99, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (403 : Vertex) (451 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 88 = false ∨ valuation q 99 = false ∨ valuation q 113 = false := by
  rw [value88, value99, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (403 : Vertex) (451 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 88 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value88, value109, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (403 : Vertex) (466 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 99 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value99, value109, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (451 : Vertex) (466 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 68 = false ∨ valuation q 89 = false ∨ valuation q 108 = false := by
  rw [value68, value89, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (340 : Vertex) (404 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 89 = false ∨ valuation q 100 = false ∨ valuation q 108 = false := by
  rw [value89, value100, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (404 : Vertex) (452 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 89 = false ∨ valuation q 108 = false ∨ valuation q 112 = false := by
  rw [value89, value108, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (404 : Vertex) (464 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 229 = true ∨ valuation q 68 = true ∨ valuation q 100 = true ∨ valuation q 108 = true ∨ valuation q 112 = true ∨ valuation q 115 = true := by
  rw [value68, value100, value108, value111, value112, value115, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(340 : Vertex), (452 : Vertex), (464 : Vertex), (470 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (404 : Vertex) [(340 : Vertex), (452 : Vertex), (464 : Vertex), (470 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 229 = true ∨ valuation q 68 = true ∨ valuation q 89 = true ∨ valuation q 100 = true ∨ valuation q 112 = true ∨ valuation q 115 = true := by
  rw [value68, value89, value100, value111, value112, value115, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(340 : Vertex), (404 : Vertex), (452 : Vertex), (470 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (464 : Vertex) [(340 : Vertex), (404 : Vertex), (452 : Vertex), (470 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 44 = false ∨ valuation q 70 = false ∨ valuation q 113 = false := by
  rw [value44, value70, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (342 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 44 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value44, value109, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 44 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value44, value109, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (466 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 44 = false ∨ valuation q 109 = false ∨ valuation q 117 = false := by
  rw [value44, value109, value112, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 44 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value44, value111, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 44 = false ∨ valuation q 111 = false ∨ valuation q 117 = false := by
  rw [value44, value111, value112, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (468 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 44 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value44, value112, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (471 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 70 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value70, value109, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (342 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 70 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value70, value109, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (342 : Vertex) (466 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 70 = false ∨ valuation q 109 = false ∨ valuation q 117 = false := by
  rw [value70, value109, value112, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (342 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E096.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112096
