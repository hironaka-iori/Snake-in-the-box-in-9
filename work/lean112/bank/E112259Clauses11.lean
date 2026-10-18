import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 15 = false ∨ valuation q 62 = false ∨ valuation q 74 = false := by
  rw [value15, value62, value71, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (27 : Vertex) (139 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 15 = false ∨ valuation q 66 = false ∨ valuation q 74 = false := by
  rw [value15, value66, value71, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (27 : Vertex) (147 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 74 = false := by
  rw [value62, value66, value71, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (139 : Vertex) (147 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value62, value66, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (155 : Vertex) (139 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 187 = true ∨ valuation q 62 = true ∨ valuation q 66 = true ∨ valuation q 74 = true := by
  rw [value62, value66, value71, value74, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(139 : Vertex), (147 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (27 : Vertex) [(139 : Vertex), (147 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 187 = true ∨ valuation q 15 = true ∨ valuation q 66 = true ∨ valuation q 74 = true := by
  rw [value15, value66, value71, value74, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(27 : Vertex), (147 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (139 : Vertex) [(27 : Vertex), (147 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 187 = true ∨ valuation q 15 = true ∨ valuation q 62 = true ∨ valuation q 74 = true := by
  rw [value15, value62, value71, value74, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(27 : Vertex), (139 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (147 : Vertex) [(27 : Vertex), (139 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 187 = true ∨ valuation q 15 = true ∨ valuation q 62 = true ∨ valuation q 66 = true := by
  rw [value15, value62, value66, value71, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(27 : Vertex), (139 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (159 : Vertex) [(27 : Vertex), (139 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 63 = false ∨ valuation q 68 = false ∨ valuation q 74 = false := by
  rw [value63, value68, value72, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (141 : Vertex) (149 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 63 = false ∨ valuation q 68 = false ∨ valuation q 94 = false := by
  rw [value63, value68, value72, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (141 : Vertex) (149 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 63 = false ∨ valuation q 74 = false ∨ valuation q 94 = false := by
  rw [value63, value72, value74, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (141 : Vertex) (159 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 68 = false ∨ valuation q 74 = false ∨ valuation q 94 = false := by
  rw [value68, value72, value74, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (149 : Vertex) (159 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 188 = true ∨ valuation q 63 = true ∨ valuation q 74 = true ∨ valuation q 94 = true := by
  rw [value63, value72, value74, value94, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (157 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(141 : Vertex), (159 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (157 : Vertex) (149 : Vertex) [(141 : Vertex), (159 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 17 = false ∨ valuation q 64 = false ∨ valuation q 69 = false := by
  rw [value17, value64, value69, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (30 : Vertex) (142 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 17 = false ∨ valuation q 64 = false ∨ valuation q 74 = false := by
  rw [value17, value64, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (30 : Vertex) (142 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 17 = false ∨ valuation q 64 = false ∨ valuation q 95 = false := by
  rw [value17, value64, value73, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (30 : Vertex) (142 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 17 = false ∨ valuation q 69 = false ∨ valuation q 74 = false := by
  rw [value17, value69, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (30 : Vertex) (150 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 17 = false ∨ valuation q 69 = false ∨ valuation q 95 = false := by
  rw [value17, value69, value73, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (30 : Vertex) (150 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 17 = false ∨ valuation q 74 = false ∨ valuation q 95 = false := by
  rw [value17, value73, value74, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (30 : Vertex) (159 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 64 = false ∨ valuation q 69 = false ∨ valuation q 74 = false := by
  rw [value64, value69, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (142 : Vertex) (150 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 64 = false ∨ valuation q 69 = false ∨ valuation q 95 = false := by
  rw [value64, value69, value73, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (142 : Vertex) (150 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 64 = false ∨ valuation q 74 = false ∨ valuation q 95 = false := by
  rw [value64, value73, value74, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (142 : Vertex) (159 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 69 = false ∨ valuation q 74 = false ∨ valuation q 95 = false := by
  rw [value69, value73, value74, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (150 : Vertex) (159 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 18 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value18, value72, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (159 : Vertex) (31 : Vertex) (157 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 190 = true ∨ valuation q 71 = true ∨ valuation q 72 = true ∨ valuation q 73 = true := by
  rw [value71, value72, value73, value74, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(155 : Vertex), (157 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (31 : Vertex) [(155 : Vertex), (157 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 190 = true ∨ valuation q 18 = true ∨ valuation q 72 = true ∨ valuation q 73 = true := by
  rw [value18, value72, value73, value74, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(31 : Vertex), (157 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (155 : Vertex) [(31 : Vertex), (157 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 190 = true ∨ valuation q 18 = true ∨ valuation q 71 = true ∨ valuation q 73 = true := by
  rw [value18, value71, value73, value74, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (157 : Vertex) → w ∈ [(31 : Vertex), (155 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (157 : Vertex) [(31 : Vertex), (155 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 190 = true ∨ valuation q 18 = true ∨ valuation q 71 = true ∨ valuation q 72 = true := by
  rw [value18, value71, value72, value74, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(31 : Vertex), (155 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (158 : Vertex) [(31 : Vertex), (155 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 54 = false ∨ valuation q 76 = false ∨ valuation q 79 = false := by
  rw [value54, value75, value76, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (128 : Vertex) (161 : Vertex) (164 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 54 = false ∨ valuation q 76 = false ∨ valuation q 81 = false := by
  rw [value54, value75, value76, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (128 : Vertex) (161 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 54 = false ∨ valuation q 76 = false ∨ valuation q 86 = false := by
  rw [value54, value75, value76, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (128 : Vertex) (161 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 54 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value54, value75, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (128 : Vertex) (162 : Vertex) (164 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E259.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112259
