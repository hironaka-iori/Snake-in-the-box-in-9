import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 183 = true ∨ valuation q 51 = true ∨ valuation q 54 = true ∨ valuation q 65 = true := by
  rw [value51, value54, value55, value65, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(150 : Vertex), (154 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (414 : Vertex) [(150 : Vertex), (154 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 64 = false := by
  rw [value56, value57, value58, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (194 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 184 = true ∨ valuation q 58 = true ∨ valuation q 64 = true := by
  rw [value56, value58, value64, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(194 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (193 : Vertex) [(194 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 184 = true ∨ valuation q 57 = true ∨ valuation q 64 = true := by
  rw [value56, value57, value64, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(193 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (194 : Vertex) [(193 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 184 = true ∨ valuation q 57 = true ∨ valuation q 58 = true := by
  rw [value56, value57, value58, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(193 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (208 : Vertex) [(193 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 185 = true ∨ valuation q 59 = true := by
  rw [value57, value59, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(197 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (192 : Vertex) [(197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 185 = true ∨ valuation q 56 = true := by
  rw [value56, value57, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(192 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (197 : Vertex) [(192 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 58 = true := by
  rw [value58, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (194 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 56 = true ∨ valuation q 60 = true := by
  rw [value56, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ∈ [(192 : Vertex), (202 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (194 : Vertex) [(192 : Vertex), (202 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value56, value60, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (194 : Vertex) (192 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 186 = true ∨ valuation q 60 = true := by
  rw [value58, value60, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(202 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (192 : Vertex) [(202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 186 = true ∨ valuation q 56 = true := by
  rw [value56, value58, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(192 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (202 : Vertex) [(192 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 23 = false ∨ valuation q 40 = false ∨ valuation q 67 = false := by
  rw [value23, value40, value59, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (133 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 23 = false ∨ valuation q 57 = false ∨ valuation q 67 = false := by
  rw [value23, value57, value59, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (193 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 40 = false ∨ valuation q 57 = false ∨ valuation q 67 = false := by
  rw [value40, value57, value59, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (133 : Vertex) (193 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 187 = true ∨ valuation q 23 = true ∨ valuation q 40 = true ∨ valuation q 57 = true := by
  rw [value23, value40, value57, value59, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (197 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(69 : Vertex), (133 : Vertex), (193 : Vertex)] := by decide
  have hg := other_cover q (197 : Vertex) (229 : Vertex) [(69 : Vertex), (133 : Vertex), (193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 45 = false ∨ valuation q 58 = false ∨ valuation q 62 = false := by
  rw [value45, value58, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (138 : Vertex) (194 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 188 = true ∨ valuation q 45 = true ∨ valuation q 62 = true := by
  rw [value45, value60, value62, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(138 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (194 : Vertex) [(138 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 188 = true ∨ valuation q 45 = true ∨ valuation q 58 = true := by
  rw [value45, value58, value60, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(138 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (206 : Vertex) [(138 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 189 = true := by
  rw [value61, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (204 : Vertex) (206 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 60 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value60, value62, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (202 : Vertex) (207 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 190 = true ∨ valuation q 61 = true ∨ valuation q 63 = true ∨ valuation q 65 = true := by
  rw [value61, value62, value63, value65, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(204 : Vertex), (207 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (202 : Vertex) [(204 : Vertex), (207 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 190 = true ∨ valuation q 60 = true ∨ valuation q 61 = true ∨ valuation q 65 = true := by
  rw [value60, value61, value62, value65, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(202 : Vertex), (204 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (207 : Vertex) [(202 : Vertex), (204 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 190 = true ∨ valuation q 60 = true ∨ valuation q 61 = true ∨ valuation q 63 = true := by
  rw [value60, value61, value62, value63, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(202 : Vertex), (204 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (222 : Vertex) [(202 : Vertex), (204 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 191 = true ∨ valuation q 62 = true := by
  rw [value62, value63, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(206 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (79 : Vertex) [(206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 191 = true ∨ valuation q 29 = true := by
  rw [value29, value63, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(79 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (206 : Vertex) [(79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 30 = false ∨ valuation q 48 = false ∨ valuation q 56 = false := by
  rw [value30, value48, value56, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (144 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 192 = true ∨ valuation q 48 = true ∨ valuation q 56 = true := by
  rw [value48, value56, value64, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(144 : Vertex), (192 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (80 : Vertex) [(144 : Vertex), (192 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 192 = true ∨ valuation q 30 = true ∨ valuation q 56 = true := by
  rw [value30, value56, value64, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(80 : Vertex), (192 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (144 : Vertex) [(80 : Vertex), (192 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 192 = true ∨ valuation q 30 = true ∨ valuation q 48 = true := by
  rw [value30, value48, value64, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(80 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (192 : Vertex) [(80 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 37 = false ∨ valuation q 55 = false ∨ valuation q 62 = false := by
  rw [value37, value55, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (158 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 193 = true ∨ valuation q 55 = true ∨ valuation q 62 = true := by
  rw [value55, value62, value65, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(158 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (94 : Vertex) [(158 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block11 (q : Snake 81) (h : Conditions q) : B112E055.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112055
