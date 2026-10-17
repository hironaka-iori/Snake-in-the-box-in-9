import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 46 = true ∨ valuation q 67 = true ∨ valuation q 119 = true := by
  rw [value46, value66, value67, value119, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(184 : Vertex), (249 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (232 : Vertex) [(184 : Vertex), (249 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 46 = true ∨ valuation q 55 = true ∨ valuation q 119 = true := by
  rw [value46, value55, value66, value119, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(184 : Vertex), (232 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (249 : Vertex) [(184 : Vertex), (232 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 46 = true ∨ valuation q 55 = true ∨ valuation q 67 = true := by
  rw [value46, value55, value66, value67, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(184 : Vertex), (232 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (504 : Vertex) [(184 : Vertex), (232 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 29 = false ∨ valuation q 47 = false ∨ valuation q 60 = false := by
  rw [value29, value47, value60, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (121 : Vertex) (185 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 29 = false ∨ valuation q 47 = false ∨ valuation q 66 = false := by
  rw [value29, value47, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (121 : Vertex) (185 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 29 = false ∨ valuation q 47 = false ∨ valuation q 68 = false := by
  rw [value29, value47, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (121 : Vertex) (185 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 29 = false ∨ valuation q 47 = false ∨ valuation q 69 = false := by
  rw [value29, value47, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (121 : Vertex) (185 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 29 = false ∨ valuation q 60 = false ∨ valuation q 66 = false := by
  rw [value29, value60, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (121 : Vertex) (241 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 29 = false ∨ valuation q 60 = false ∨ valuation q 68 = false := by
  rw [value29, value60, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (121 : Vertex) (241 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 29 = false ∨ valuation q 60 = false ∨ valuation q 69 = false := by
  rw [value29, value60, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (121 : Vertex) (241 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 29 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value29, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (121 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 29 = false ∨ valuation q 66 = false ∨ valuation q 69 = false := by
  rw [value29, value66, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (121 : Vertex) (248 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 29 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value29, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (121 : Vertex) (251 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 47 = false ∨ valuation q 60 = false ∨ valuation q 66 = false := by
  rw [value47, value60, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (185 : Vertex) (241 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 47 = false ∨ valuation q 60 = false ∨ valuation q 68 = false := by
  rw [value47, value60, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (185 : Vertex) (241 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 47 = false ∨ valuation q 60 = false ∨ valuation q 69 = false := by
  rw [value47, value60, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (185 : Vertex) (241 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 47 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value47, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (185 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 47 = false ∨ valuation q 66 = false ∨ valuation q 69 = false := by
  rw [value47, value66, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (185 : Vertex) (248 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 47 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value47, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (185 : Vertex) (251 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 60 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value60, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (241 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 60 = false ∨ valuation q 66 = false ∨ valuation q 69 = false := by
  rw [value60, value66, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (241 : Vertex) (248 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 60 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value60, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (241 : Vertex) (251 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 66 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value66, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (248 : Vertex) (251 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 57 = false ∨ valuation q 62 = false ∨ valuation q 67 = false := by
  rw [value57, value62, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (243 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 57 = false ∨ valuation q 62 = false ∨ valuation q 70 = false := by
  rw [value57, value62, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (243 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 57 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value57, value67, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (249 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 57 = false ∨ valuation q 70 = false ∨ valuation q 120 = false := by
  rw [value57, value68, value70, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (255 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 62 = false ∨ valuation q 70 = false ∨ valuation q 120 = false := by
  rw [value62, value68, value70, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (243 : Vertex) (255 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 62 = true ∨ valuation q 67 = true ∨ valuation q 70 = true ∨ valuation q 120 = true := by
  rw [value62, value67, value68, value70, value120, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(243 : Vertex), (249 : Vertex), (255 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (235 : Vertex) [(243 : Vertex), (249 : Vertex), (255 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 57 = true ∨ valuation q 67 = true ∨ valuation q 70 = true ∨ valuation q 120 = true := by
  rw [value57, value67, value68, value70, value120, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(235 : Vertex), (249 : Vertex), (255 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (243 : Vertex) [(235 : Vertex), (249 : Vertex), (255 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 57 = true ∨ valuation q 62 = true ∨ valuation q 67 = true ∨ valuation q 120 = true := by
  rw [value57, value62, value67, value68, value120, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(235 : Vertex), (243 : Vertex), (249 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (255 : Vertex) [(235 : Vertex), (243 : Vertex), (249 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 57 = true ∨ valuation q 62 = true ∨ valuation q 67 = true ∨ valuation q 70 = true := by
  rw [value57, value62, value67, value68, value70, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(235 : Vertex), (243 : Vertex), (249 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (507 : Vertex) [(235 : Vertex), (243 : Vertex), (249 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block12 (q : Snake 81) (h : Conditions q) : B112E020.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112020
