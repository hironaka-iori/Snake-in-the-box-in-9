import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 183 = true ∨ valuation q 28 = true ∨ valuation q 46 = true ∨ valuation q 68 = true ∨ valuation q 72 = true := by
  rw [value28, value46, value67, value68, value72, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(48 : Vertex), (144 : Vertex), (178 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (180 : Vertex) [(48 : Vertex), (144 : Vertex), (178 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 29 = false ∨ valuation q 58 = false ∨ valuation q 67 = false := by
  rw [value29, value58, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (50 : Vertex) (162 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 29 = false ∨ valuation q 58 = false ∨ valuation q 69 = false := by
  rw [value29, value58, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (50 : Vertex) (162 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 29 = false ∨ valuation q 67 = false ∨ valuation q 69 = false := by
  rw [value29, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (50 : Vertex) (176 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 184 = true ∨ valuation q 58 = true ∨ valuation q 67 = true ∨ valuation q 69 = true ∨ valuation q 74 = true := by
  rw [value58, value67, value68, value69, value74, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (178 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(162 : Vertex), (176 : Vertex), (179 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (178 : Vertex) (50 : Vertex) [(162 : Vertex), (176 : Vertex), (179 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 48 = false ∨ valuation q 68 = false ∨ valuation q 71 = false := by
  rw [value48, value68, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (147 : Vertex) (178 : Vertex) (183 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 48 = false ∨ valuation q 68 = false ∨ valuation q 75 = false := by
  rw [value48, value68, value69, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (147 : Vertex) (178 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 48 = false ∨ valuation q 68 = false ∨ valuation q 111 = false := by
  rw [value48, value68, value69, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (147 : Vertex) (178 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 48 = false ∨ valuation q 71 = false ∨ valuation q 75 = false := by
  rw [value48, value69, value71, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (147 : Vertex) (183 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 68 = false ∨ valuation q 71 = false ∨ valuation q 75 = false := by
  rw [value68, value69, value71, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (178 : Vertex) (183 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 68 = false ∨ valuation q 71 = false ∨ valuation q 111 = false := by
  rw [value68, value69, value71, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (178 : Vertex) (183 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 75 = false ∨ valuation q 111 = false := by
  rw [value69, value71, value75, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (183 : Vertex) (187 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 185 = true ∨ valuation q 48 = true ∨ valuation q 68 = true ∨ valuation q 75 = true ∨ valuation q 111 = true := by
  rw [value48, value68, value69, value75, value111, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(147 : Vertex), (178 : Vertex), (187 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (183 : Vertex) [(147 : Vertex), (178 : Vertex), (187 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 186 = true ∨ valuation q 76 = true := by
  rw [value70, value76, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (180 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(188 : Vertex)] := by decide
  have hg := other_cover q (180 : Vertex) (176 : Vertex) [(188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 186 = true ∨ valuation q 67 = true := by
  rw [value67, value70, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (180 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(176 : Vertex)] := by decide
  have hg := other_cover q (180 : Vertex) (188 : Vertex) [(176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 31 = false ∨ valuation q 69 = false ∨ valuation q 77 = false := by
  rw [value31, value69, value71, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (179 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 187 = true ∨ valuation q 69 = true ∨ valuation q 77 = true := by
  rw [value69, value71, value77, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(179 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (55 : Vertex) [(179 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 187 = true ∨ valuation q 31 = true ∨ valuation q 77 = true := by
  rw [value31, value71, value77, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(55 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (179 : Vertex) [(55 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 187 = true ∨ valuation q 31 = true ∨ valuation q 69 = true := by
  rw [value31, value69, value71, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (191 : Vertex) → w ∈ [(55 : Vertex), (179 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (191 : Vertex) [(55 : Vertex), (179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 51 = false ∨ valuation q 61 = false ∨ valuation q 67 = false := by
  rw [value51, value61, value67, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (152 : Vertex) (168 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 51 = false ∨ valuation q 61 = false ∨ valuation q 73 = false := by
  rw [value51, value61, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (152 : Vertex) (168 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 51 = false ∨ valuation q 61 = false ∨ valuation q 76 = false := by
  rw [value51, value61, value72, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (152 : Vertex) (168 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 51 = false ∨ valuation q 67 = false ∨ valuation q 73 = false := by
  rw [value51, value67, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (152 : Vertex) (176 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 51 = false ∨ valuation q 67 = false ∨ valuation q 76 = false := by
  rw [value51, value67, value72, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (152 : Vertex) (176 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 51 = false ∨ valuation q 73 = false ∨ valuation q 76 = false := by
  rw [value51, value72, value73, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (152 : Vertex) (185 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 51 = false ∨ valuation q 74 = false ∨ valuation q 76 = false := by
  rw [value51, value72, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (152 : Vertex) (186 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 61 = false ∨ valuation q 67 = false ∨ valuation q 73 = false := by
  rw [value61, value67, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (176 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 61 = false ∨ valuation q 73 = false ∨ valuation q 76 = false := by
  rw [value61, value72, value73, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (185 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 188 = true ∨ valuation q 61 = true ∨ valuation q 67 = true ∨ valuation q 73 = true ∨ valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 78 = true := by
  rw [value61, value67, value72, value73, value74, value76, value78, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (184 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(168 : Vertex), (176 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (184 : Vertex) (152 : Vertex) [(168 : Vertex), (176 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 188 = true ∨ valuation q 51 = true ∨ valuation q 61 = true ∨ valuation q 73 = true ∨ valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 78 = true := by
  rw [value51, value61, value72, value73, value74, value76, value78, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (184 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(152 : Vertex), (168 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (184 : Vertex) (176 : Vertex) [(152 : Vertex), (168 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 188 = true ∨ valuation q 51 = true ∨ valuation q 61 = true ∨ valuation q 67 = true ∨ valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 78 = true := by
  rw [value51, value61, value67, value72, value74, value76, value78, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (184 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(152 : Vertex), (168 : Vertex), (176 : Vertex), (186 : Vertex), (188 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (184 : Vertex) (185 : Vertex) [(152 : Vertex), (168 : Vertex), (176 : Vertex), (186 : Vertex), (188 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 188 = true ∨ valuation q 51 = true ∨ valuation q 61 = true ∨ valuation q 67 = true ∨ valuation q 73 = true ∨ valuation q 76 = true ∨ valuation q 78 = true := by
  rw [value51, value61, value67, value72, value73, value76, value78, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (184 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(152 : Vertex), (168 : Vertex), (176 : Vertex), (185 : Vertex), (188 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (184 : Vertex) (186 : Vertex) [(152 : Vertex), (168 : Vertex), (176 : Vertex), (185 : Vertex), (188 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block12 (q : Snake 81) (h : Conditions q) : B112E257.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112257
