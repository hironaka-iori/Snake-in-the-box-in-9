import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 59 = true ∨ valuation q 65 = true := by
  rw [value59, value60, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ∈ [(195 : Vertex), (207 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (199 : Vertex) [(195 : Vertex), (207 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 177 = true ∨ valuation q 65 = true := by
  rw [value60, value65, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (195 : Vertex) [(207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 177 = true ∨ valuation q 59 = true := by
  rw [value59, value60, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(195 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (207 : Vertex) [(195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 44 = false ∨ valuation q 57 = false ∨ valuation q 63 = false := by
  rw [value44, value57, value61, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 178 = true ∨ valuation q 57 = true ∨ valuation q 63 = true := by
  rw [value57, value61, value63, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(193 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (137 : Vertex) [(193 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 178 = true ∨ valuation q 44 = true ∨ valuation q 63 = true := by
  rw [value44, value61, value63, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(137 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (193 : Vertex) [(137 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 178 = true ∨ valuation q 44 = true ∨ valuation q 57 = true := by
  rw [value44, value57, value61, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(137 : Vertex), (193 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (205 : Vertex) [(137 : Vertex), (193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 179 = true ∨ valuation q 64 = true ∨ valuation q 72 = true := by
  rw [value62, value64, value72, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(206 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (205 : Vertex) [(206 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 179 = true ∨ valuation q 63 = true ∨ valuation q 72 = true := by
  rw [value62, value63, value72, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(205 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (206 : Vertex) [(205 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 179 = true ∨ valuation q 63 = true ∨ valuation q 64 = true := by
  rw [value62, value63, value64, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(205 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (220 : Vertex) [(205 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 65 = false := by
  rw [value61, value62, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (201 : Vertex) (204 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 180 = true ∨ valuation q 62 = true ∨ valuation q 65 = true := by
  rw [value62, value63, value65, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(204 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (201 : Vertex) [(204 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 180 = true ∨ valuation q 61 = true ∨ valuation q 65 = true := by
  rw [value61, value63, value65, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(201 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (204 : Vertex) [(201 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 180 = true ∨ valuation q 61 = true ∨ valuation q 62 = true := by
  rw [value61, value62, value63, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(201 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (207 : Vertex) [(201 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 30 = false ∨ valuation q 46 = false ∨ valuation q 62 = false := by
  rw [value30, value46, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (142 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 30 = false ∨ valuation q 46 = false ∨ valuation q 65 = false := by
  rw [value30, value46, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (142 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 30 = false ∨ valuation q 46 = false ∨ valuation q 73 = false := by
  rw [value30, value46, value64, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (142 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 30 = false ∨ valuation q 46 = false ∨ valuation q 112 = false := by
  rw [value30, value46, value64, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (142 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 30 = false ∨ valuation q 62 = false ∨ valuation q 65 = false := by
  rw [value30, value62, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (204 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 30 = false ∨ valuation q 62 = false ∨ valuation q 73 = false := by
  rw [value30, value62, value64, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (204 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 30 = false ∨ valuation q 62 = false ∨ valuation q 112 = false := by
  rw [value30, value62, value64, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (204 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 30 = false ∨ valuation q 65 = false ∨ valuation q 73 = false := by
  rw [value30, value64, value65, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (207 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 30 = false ∨ valuation q 65 = false ∨ valuation q 112 = false := by
  rw [value30, value64, value65, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (207 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 30 = false ∨ valuation q 73 = false ∨ valuation q 112 = false := by
  rw [value30, value64, value73, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (222 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 46 = false ∨ valuation q 62 = false ∨ valuation q 65 = false := by
  rw [value46, value62, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (142 : Vertex) (204 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 46 = false ∨ valuation q 62 = false ∨ valuation q 73 = false := by
  rw [value46, value62, value64, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (142 : Vertex) (204 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 46 = false ∨ valuation q 62 = false ∨ valuation q 112 = false := by
  rw [value46, value62, value64, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (142 : Vertex) (204 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 46 = false ∨ valuation q 65 = false ∨ valuation q 73 = false := by
  rw [value46, value64, value65, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (142 : Vertex) (207 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 46 = false ∨ valuation q 65 = false ∨ valuation q 112 = false := by
  rw [value46, value64, value65, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (142 : Vertex) (207 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 46 = false ∨ valuation q 73 = false ∨ valuation q 112 = false := by
  rw [value46, value64, value73, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (142 : Vertex) (222 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 73 = false := by
  rw [value62, value64, value65, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (204 : Vertex) (207 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 112 = false := by
  rw [value62, value64, value65, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (204 : Vertex) (207 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E115.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112115
