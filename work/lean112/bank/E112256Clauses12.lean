import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 55 = false ∨ valuation q 66 = false := by
  rw [value55, value66, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (228 : Vertex) (224 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 184 = true ∨ valuation q 55 = true ∨ valuation q 66 = true := by
  rw [value55, value57, value66, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (228 : Vertex) w → w ∈ region → w ≠ (196 : Vertex) → w ∈ [(224 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (228 : Vertex) (196 : Vertex) [(224 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 184 = true ∨ valuation q 39 = true ∨ valuation q 66 = true := by
  rw [value39, value57, value66, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (228 : Vertex) w → w ∈ region → w ≠ (224 : Vertex) → w ∈ [(196 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (228 : Vertex) (224 : Vertex) [(196 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 184 = true ∨ valuation q 39 = true ∨ valuation q 55 = true := by
  rw [value39, value55, value57, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (228 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(196 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (228 : Vertex) (244 : Vertex) [(196 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 58 = true := by
  rw [value58, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (231 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 22 = true ∨ valuation q 56 = true := by
  rw [value22, value56, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (231 : Vertex) w → w ∈ region → w ∈ [(103 : Vertex), (227 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (231 : Vertex) [(103 : Vertex), (227 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 22 = false ∨ valuation q 56 = false := by
  rw [value22, value56, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (231 : Vertex) (103 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 185 = true ∨ valuation q 56 = true := by
  rw [value56, value58, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (231 : Vertex) w → w ∈ region → w ≠ (103 : Vertex) → w ∈ [(227 : Vertex)] := by decide
  have hg := other_cover q (231 : Vertex) (103 : Vertex) [(227 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 185 = true ∨ valuation q 22 = true := by
  rw [value22, value58, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (231 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(103 : Vertex)] := by decide
  have hg := other_cover q (231 : Vertex) (227 : Vertex) [(103 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 42 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value42, value59, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (202 : Vertex) (235 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 42 = false ∨ valuation q 60 = false ∨ valuation q 70 = false := by
  rw [value42, value59, value60, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (202 : Vertex) (235 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 42 = false ∨ valuation q 62 = false ∨ valuation q 70 = false := by
  rw [value42, value59, value62, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (202 : Vertex) (238 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 62 = false ∨ valuation q 70 = false := by
  rw [value59, value60, value62, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (235 : Vertex) (238 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 186 = true ∨ valuation q 42 = true ∨ valuation q 60 = true ∨ valuation q 70 = true := by
  rw [value42, value59, value60, value70, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(202 : Vertex), (235 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (238 : Vertex) [(202 : Vertex), (235 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 186 = true ∨ valuation q 42 = true ∨ valuation q 60 = true ∨ valuation q 62 = true := by
  rw [value42, value59, value60, value62, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(202 : Vertex), (235 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (250 : Vertex) [(202 : Vertex), (235 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 24 = true ∨ valuation q 56 = true ∨ valuation q 59 = true ∨ valuation q 71 = true := by
  rw [value24, value56, value59, value60, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ∈ [(107 : Vertex), (227 : Vertex), (234 : Vertex), (251 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (235 : Vertex) [(107 : Vertex), (227 : Vertex), (234 : Vertex), (251 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 24 = false ∨ valuation q 56 = false ∨ valuation q 59 = false := by
  rw [value24, value56, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 24 = false ∨ valuation q 56 = false ∨ valuation q 71 = false := by
  rw [value24, value56, value60, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (227 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 187 = true ∨ valuation q 56 = true ∨ valuation q 59 = true ∨ valuation q 71 = true := by
  rw [value56, value59, value60, value71, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ≠ (107 : Vertex) → w ∈ [(227 : Vertex), (234 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (235 : Vertex) (107 : Vertex) [(227 : Vertex), (234 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 187 = true ∨ valuation q 24 = true ∨ valuation q 59 = true ∨ valuation q 71 = true := by
  rw [value24, value59, value60, value71, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(107 : Vertex), (234 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (235 : Vertex) (227 : Vertex) [(107 : Vertex), (234 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 187 = true ∨ valuation q 24 = true ∨ valuation q 56 = true ∨ valuation q 59 = true := by
  rw [value24, value56, value59, value60, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(107 : Vertex), (227 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (235 : Vertex) (251 : Vertex) [(107 : Vertex), (227 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 61 = true := by
  rw [value61, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (237 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 72 = true := by
  rw [value61, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (237 : Vertex) w → w ∈ region → w ∈ [(253 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (237 : Vertex) [(253 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 188 = true := by
  rw [value61, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (237 : Vertex) w → w ∈ region → w ≠ (253 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (237 : Vertex) (253 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 62 = true := by
  rw [value62, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (238 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 26 = true ∨ valuation q 59 = true ∨ valuation q 73 = true := by
  rw [value26, value59, value62, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ∈ [(110 : Vertex), (234 : Vertex), (254 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (238 : Vertex) [(110 : Vertex), (234 : Vertex), (254 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 26 = false ∨ valuation q 59 = false ∨ valuation q 73 = false := by
  rw [value26, value59, value62, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (238 : Vertex) (110 : Vertex) (234 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 26 = false ∨ valuation q 73 = false := by
  rw [value26, value73, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (238 : Vertex) (110 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 189 = true ∨ valuation q 59 = true ∨ valuation q 73 = true := by
  rw [value59, value62, value73, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (110 : Vertex) → w ∈ [(234 : Vertex), (254 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (110 : Vertex) [(234 : Vertex), (254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 189 = true ∨ valuation q 26 = true ∨ valuation q 73 = true := by
  rw [value26, value62, value73, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (234 : Vertex) → w ∈ [(110 : Vertex), (254 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (234 : Vertex) [(110 : Vertex), (254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 189 = true ∨ valuation q 26 = true ∨ valuation q 59 = true := by
  rw [value26, value59, value62, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(110 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (254 : Vertex) [(110 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 63 = true := by
  rw [value63, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (240 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem block12 (q : Snake 81) (h : Conditions q) : B112E256.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112256
