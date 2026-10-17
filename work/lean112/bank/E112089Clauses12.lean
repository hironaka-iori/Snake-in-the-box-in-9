import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value19, value56, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (195 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 58 = false ∨ valuation q 70 = false := by
  rw [value19, value56, value58, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (195 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 58 = false ∨ valuation q 108 = false := by
  rw [value19, value56, value58, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (195 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 59 = false ∨ valuation q 70 = false := by
  rw [value19, value56, value59, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (197 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 59 = false ∨ valuation q 108 = false := by
  rw [value19, value56, value59, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (197 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 70 = false ∨ valuation q 108 = false := by
  rw [value19, value56, value70, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (209 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 36 = false ∨ valuation q 58 = false ∨ valuation q 63 = false := by
  rw [value36, value56, value58, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (129 : Vertex) (195 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 36 = false ∨ valuation q 59 = false ∨ valuation q 63 = false := by
  rw [value36, value56, value59, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (129 : Vertex) (197 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 36 = false ∨ valuation q 59 = false ∨ valuation q 108 = false := by
  rw [value36, value56, value59, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (129 : Vertex) (197 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 70 = false := by
  rw [value56, value58, value59, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (195 : Vertex) (197 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 108 = false := by
  rw [value56, value58, value59, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (195 : Vertex) (197 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 63 = false ∨ valuation q 70 = false := by
  rw [value56, value58, value63, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (195 : Vertex) (201 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 70 = false ∨ valuation q 108 = false := by
  rw [value56, value58, value70, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (195 : Vertex) (209 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 59 = false ∨ valuation q 63 = false ∨ valuation q 70 = false := by
  rw [value56, value59, value63, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (197 : Vertex) (201 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 59 = false ∨ valuation q 63 = false ∨ valuation q 108 = false := by
  rw [value56, value59, value63, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (197 : Vertex) (201 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 59 = false ∨ valuation q 70 = false ∨ valuation q 108 = false := by
  rw [value56, value59, value70, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (197 : Vertex) (209 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 180 = true ∨ valuation q 36 = true ∨ valuation q 58 = true ∨ valuation q 59 = true ∨ valuation q 63 = true ∨ valuation q 70 = true ∨ valuation q 108 = true := by
  rw [value36, value56, value58, value59, value63, value70, value108, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(129 : Vertex), (195 : Vertex), (197 : Vertex), (201 : Vertex), (209 : Vertex), (449 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (65 : Vertex) [(129 : Vertex), (195 : Vertex), (197 : Vertex), (201 : Vertex), (209 : Vertex), (449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 180 = true ∨ valuation q 19 = true ∨ valuation q 36 = true ∨ valuation q 58 = true ∨ valuation q 59 = true ∨ valuation q 70 = true ∨ valuation q 108 = true := by
  rw [value19, value36, value56, value58, value59, value70, value108, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(65 : Vertex), (129 : Vertex), (195 : Vertex), (197 : Vertex), (209 : Vertex), (449 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (201 : Vertex) [(65 : Vertex), (129 : Vertex), (195 : Vertex), (197 : Vertex), (209 : Vertex), (449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 180 = true ∨ valuation q 19 = true ∨ valuation q 36 = true ∨ valuation q 58 = true ∨ valuation q 59 = true ∨ valuation q 63 = true ∨ valuation q 70 = true := by
  rw [value19, value36, value56, value58, value59, value63, value70, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(65 : Vertex), (129 : Vertex), (195 : Vertex), (197 : Vertex), (201 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (449 : Vertex) [(65 : Vertex), (129 : Vertex), (195 : Vertex), (197 : Vertex), (201 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 20 = false ∨ valuation q 37 = false ∨ valuation q 71 = false := by
  rw [value20, value37, value57, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (130 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 20 = false ∨ valuation q 37 = false ∨ valuation q 109 = false := by
  rw [value20, value37, value57, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (130 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 20 = false ∨ valuation q 58 = false ∨ valuation q 71 = false := by
  rw [value20, value57, value58, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (195 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 20 = false ∨ valuation q 58 = false ∨ valuation q 109 = false := by
  rw [value20, value57, value58, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (195 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 20 = false ∨ valuation q 71 = false ∨ valuation q 109 = false := by
  rw [value20, value57, value71, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (210 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 37 = false ∨ valuation q 58 = false ∨ valuation q 71 = false := by
  rw [value37, value57, value58, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (130 : Vertex) (195 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 37 = false ∨ valuation q 58 = false ∨ valuation q 109 = false := by
  rw [value37, value57, value58, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (130 : Vertex) (195 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 37 = false ∨ valuation q 71 = false ∨ valuation q 109 = false := by
  rw [value37, value57, value71, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (130 : Vertex) (210 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 71 = false := by
  rw [value57, value58, value60, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (195 : Vertex) (198 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 71 = false ∨ valuation q 109 = false := by
  rw [value57, value58, value71, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (195 : Vertex) (210 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 181 = true ∨ valuation q 37 = true ∨ valuation q 58 = true ∨ valuation q 60 = true ∨ valuation q 71 = true ∨ valuation q 109 = true := by
  rw [value37, value57, value58, value60, value71, value109, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(130 : Vertex), (195 : Vertex), (198 : Vertex), (210 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (66 : Vertex) [(130 : Vertex), (195 : Vertex), (198 : Vertex), (210 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 181 = true ∨ valuation q 20 = true ∨ valuation q 58 = true ∨ valuation q 60 = true ∨ valuation q 71 = true ∨ valuation q 109 = true := by
  rw [value20, value57, value58, value60, value71, value109, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(66 : Vertex), (195 : Vertex), (198 : Vertex), (210 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (130 : Vertex) [(66 : Vertex), (195 : Vertex), (198 : Vertex), (210 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 61 = false := by
  rw [value56, value57, value58, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (194 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E089.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112089
