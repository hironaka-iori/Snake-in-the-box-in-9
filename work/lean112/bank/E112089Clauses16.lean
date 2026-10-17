import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 41 = false ∨ valuation q 56 = false ∨ valuation q 66 = false := by
  rw [value41, value56, value63, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 41 = false ∨ valuation q 56 = false ∨ valuation q 113 = false := by
  rw [value41, value56, value63, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 41 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value41, value62, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 41 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value41, value62, value63, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 41 = false ∨ valuation q 62 = false ∨ valuation q 113 = false := by
  rw [value41, value62, value63, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 41 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value41, value63, value64, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (203 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 41 = false ∨ valuation q 64 = false ∨ valuation q 113 = false := by
  rw [value41, value63, value64, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (203 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 41 = false ∨ valuation q 66 = false ∨ valuation q 113 = false := by
  rw [value41, value63, value66, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (205 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 56 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value56, value62, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 56 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value56, value62, value63, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 56 = false ∨ valuation q 62 = false ∨ valuation q 113 = false := by
  rw [value56, value62, value63, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 56 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value56, value63, value64, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (203 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 56 = false ∨ valuation q 64 = false ∨ valuation q 113 = false := by
  rw [value56, value63, value64, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (203 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 56 = false ∨ valuation q 66 = false ∨ valuation q 113 = false := by
  rw [value56, value63, value66, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (205 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 62 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value62, value63, value64, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (200 : Vertex) (203 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 62 = false ∨ valuation q 64 = false ∨ valuation q 113 = false := by
  rw [value62, value63, value64, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (200 : Vertex) (203 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 113 = false := by
  rw [value62, value63, value66, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (200 : Vertex) (205 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 113 = false := by
  rw [value63, value64, value66, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (203 : Vertex) (205 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 187 = true ∨ valuation q 41 = true ∨ valuation q 56 = true ∨ valuation q 62 = true ∨ valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 113 = true := by
  rw [value41, value56, value62, value63, value64, value66, value113, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(137 : Vertex), (193 : Vertex), (200 : Vertex), (203 : Vertex), (205 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (73 : Vertex) [(137 : Vertex), (193 : Vertex), (200 : Vertex), (203 : Vertex), (205 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 187 = true ∨ valuation q 24 = true ∨ valuation q 41 = true ∨ valuation q 56 = true ∨ valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 113 = true := by
  rw [value24, value41, value56, value63, value64, value66, value113, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(73 : Vertex), (137 : Vertex), (193 : Vertex), (203 : Vertex), (205 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (200 : Vertex) [(73 : Vertex), (137 : Vertex), (193 : Vertex), (203 : Vertex), (205 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 64 = true := by
  rw [value64, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (203 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 43 = true ∨ valuation q 58 = true ∨ valuation q 63 = true ∨ valuation q 68 = true := by
  rw [value43, value58, value63, value64, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ∈ [(139 : Vertex), (195 : Vertex), (201 : Vertex), (207 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (203 : Vertex) [(139 : Vertex), (195 : Vertex), (201 : Vertex), (207 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 43 = false ∨ valuation q 58 = false ∨ valuation q 63 = false := by
  rw [value43, value58, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (139 : Vertex) (195 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 43 = false ∨ valuation q 63 = false ∨ valuation q 68 = false := by
  rw [value43, value63, value64, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (139 : Vertex) (201 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 43 = false ∨ valuation q 68 = false := by
  rw [value43, value68, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (203 : Vertex) (139 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 63 = false ∨ valuation q 68 = false := by
  rw [value63, value68, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (203 : Vertex) (201 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 188 = true ∨ valuation q 58 = true ∨ valuation q 63 = true ∨ valuation q 68 = true := by
  rw [value58, value63, value64, value68, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(195 : Vertex), (201 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (139 : Vertex) [(195 : Vertex), (201 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 188 = true ∨ valuation q 43 = true ∨ valuation q 63 = true ∨ valuation q 68 = true := by
  rw [value43, value63, value64, value68, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(139 : Vertex), (201 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (195 : Vertex) [(139 : Vertex), (201 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 188 = true ∨ valuation q 43 = true ∨ valuation q 58 = true ∨ valuation q 68 = true := by
  rw [value43, value58, value64, value68, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(139 : Vertex), (195 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (201 : Vertex) [(139 : Vertex), (195 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 188 = true ∨ valuation q 43 = true ∨ valuation q 58 = true ∨ valuation q 63 = true := by
  rw [value43, value58, value63, value64, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(139 : Vertex), (195 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (207 : Vertex) [(139 : Vertex), (195 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 25 = false ∨ valuation q 44 = false ∨ valuation q 62 = false := by
  rw [value25, value44, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 25 = false ∨ valuation q 44 = false ∨ valuation q 66 = false := by
  rw [value25, value44, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E089.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112089
