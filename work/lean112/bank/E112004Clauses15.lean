import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 57 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value57, value62, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (226 : Vertex) (235 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 182 = true ∨ valuation q 63 = true ∨ valuation q 65 = true := by
  rw [value62, value63, value65, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(235 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (226 : Vertex) [(235 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 182 = true ∨ valuation q 57 = true ∨ valuation q 65 = true := by
  rw [value57, value62, value65, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(226 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (235 : Vertex) [(226 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 182 = true ∨ valuation q 57 = true ∨ valuation q 63 = true := by
  rw [value57, value62, value63, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(226 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (238 : Vertex) [(226 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 40 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value40, value61, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (233 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 40 = false ∨ valuation q 62 = false := by
  rw [value40, value62, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (235 : Vertex) (171 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value61, value62, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (235 : Vertex) (233 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 183 = true ∨ valuation q 40 = true ∨ valuation q 62 = true := by
  rw [value40, value62, value63, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(171 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (235 : Vertex) (233 : Vertex) [(171 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 183 = true ∨ valuation q 40 = true ∨ valuation q 61 = true := by
  rw [value40, value61, value63, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ≠ (234 : Vertex) → w ∈ [(171 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (235 : Vertex) (234 : Vertex) [(171 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 41 = false ∨ valuation q 58 = false ∨ valuation q 65 = false := by
  rw [value41, value58, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (172 : Vertex) (228 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 184 = true ∨ valuation q 41 = true ∨ valuation q 65 = true ∨ valuation q 110 = true := by
  rw [value41, value64, value65, value110, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(172 : Vertex), (238 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (228 : Vertex) [(172 : Vertex), (238 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 184 = true ∨ valuation q 41 = true ∨ valuation q 58 = true ∨ valuation q 110 = true := by
  rw [value41, value58, value64, value110, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(172 : Vertex), (228 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (238 : Vertex) [(172 : Vertex), (228 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 60 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value60, value62, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (238 : Vertex) (230 : Vertex) (234 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 60 = false ∨ valuation q 62 = false ∨ valuation q 73 = false := by
  rw [value60, value62, value65, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (238 : Vertex) (230 : Vertex) (234 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 60 = false ∨ valuation q 64 = false ∨ valuation q 73 = false := by
  rw [value60, value64, value65, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (238 : Vertex) (230 : Vertex) (236 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 62 = false ∨ valuation q 64 = false ∨ valuation q 73 = false := by
  rw [value62, value64, value65, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (238 : Vertex) (234 : Vertex) (236 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 185 = true ∨ valuation q 60 = true ∨ valuation q 62 = true ∨ valuation q 64 = true := by
  rw [value60, value62, value64, value65, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(230 : Vertex), (234 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (254 : Vertex) [(230 : Vertex), (234 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 24 = false ∨ valuation q 44 = false ∨ valuation q 71 = false := by
  rw [value24, value44, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (112 : Vertex) (176 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 24 = false ∨ valuation q 67 = false ∨ valuation q 71 = false := by
  rw [value24, value66, value67, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (112 : Vertex) (241 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 44 = false ∨ valuation q 67 = false ∨ valuation q 71 = false := by
  rw [value44, value66, value67, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (176 : Vertex) (241 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 186 = true ∨ valuation q 24 = true ∨ valuation q 44 = true ∨ valuation q 67 = true := by
  rw [value24, value44, value66, value67, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (240 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(112 : Vertex), (176 : Vertex), (241 : Vertex)] := by decide
  have hg := other_cover q (240 : Vertex) (248 : Vertex) [(112 : Vertex), (176 : Vertex), (241 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 66 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value66, value67, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (240 : Vertex) (245 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 187 = true ∨ valuation q 68 = true ∨ valuation q 69 = true ∨ valuation q 72 = true := by
  rw [value67, value68, value69, value72, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(243 : Vertex), (245 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (240 : Vertex) [(243 : Vertex), (245 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 187 = true ∨ valuation q 66 = true ∨ valuation q 69 = true ∨ valuation q 72 = true := by
  rw [value66, value67, value69, value72, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(240 : Vertex), (245 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (243 : Vertex) [(240 : Vertex), (245 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 187 = true ∨ valuation q 66 = true ∨ valuation q 68 = true ∨ valuation q 72 = true := by
  rw [value66, value67, value68, value72, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(240 : Vertex), (243 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (245 : Vertex) [(240 : Vertex), (243 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 187 = true ∨ valuation q 66 = true ∨ valuation q 68 = true ∨ valuation q 69 = true := by
  rw [value66, value67, value68, value69, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(240 : Vertex), (243 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (249 : Vertex) [(240 : Vertex), (243 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 26 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value26, value67, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (241 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 46 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value46, value67, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (179 : Vertex) (241 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 59 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value59, value67, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (229 : Vertex) (241 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 189 = true ∨ valuation q 67 = true ∨ valuation q 70 = true := by
  rw [value67, value69, value70, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(241 : Vertex), (247 : Vertex)] := by decide
  have hg := other_cover q (245 : Vertex) (229 : Vertex) [(241 : Vertex), (247 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 49 = false ∨ valuation q 68 = false ∨ valuation q 74 = false := by
  rw [value49, value68, value70, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (247 : Vertex) (183 : Vertex) (243 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 49 = false ∨ valuation q 69 = false ∨ valuation q 74 = false := by
  rw [value49, value69, value70, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (247 : Vertex) (183 : Vertex) (245 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E004.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112004
