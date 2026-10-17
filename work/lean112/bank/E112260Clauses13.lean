import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 64 = false ∨ valuation q 68 = false ∨ valuation q 119 = false := by
  rw [value58, value64, value68, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (237 : Vertex) (245 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 185 = true ∨ valuation q 40 = true ∨ valuation q 64 = true ∨ valuation q 68 = true ∨ valuation q 119 = true := by
  rw [value40, value58, value64, value68, value119, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (101 : Vertex) → w ∈ [(197 : Vertex), (237 : Vertex), (245 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (101 : Vertex) [(197 : Vertex), (237 : Vertex), (245 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 185 = true ∨ valuation q 20 = true ∨ valuation q 40 = true ∨ valuation q 64 = true ∨ valuation q 68 = true := by
  rw [value20, value40, value58, value64, value68, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(101 : Vertex), (197 : Vertex), (237 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (485 : Vertex) [(101 : Vertex), (197 : Vertex), (237 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 21 = false ∨ valuation q 56 = false ∨ valuation q 65 = false := by
  rw [value21, value56, value59, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (230 : Vertex) (102 : Vertex) (226 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 21 = false ∨ valuation q 56 = false ∨ valuation q 69 = false := by
  rw [value21, value56, value59, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (230 : Vertex) (102 : Vertex) (226 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 21 = false ∨ valuation q 65 = false ∨ valuation q 69 = false := by
  rw [value21, value59, value65, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (230 : Vertex) (102 : Vertex) (238 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 56 = false ∨ valuation q 65 = false ∨ valuation q 69 = false := by
  rw [value56, value59, value65, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (230 : Vertex) (226 : Vertex) (238 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 186 = true ∨ valuation q 21 = true ∨ valuation q 56 = true ∨ valuation q 69 = true := by
  rw [value21, value56, value59, value69, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(102 : Vertex), (226 : Vertex), (246 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (238 : Vertex) [(102 : Vertex), (226 : Vertex), (246 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 186 = true ∨ valuation q 21 = true ∨ valuation q 56 = true ∨ valuation q 65 = true := by
  rw [value21, value56, value59, value65, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(102 : Vertex), (226 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (246 : Vertex) [(102 : Vertex), (226 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 23 = false ∨ valuation q 55 = false ∨ valuation q 121 = false := by
  rw [value23, value55, value60, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (104 : Vertex) (224 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 23 = false ∨ valuation q 63 = false ∨ valuation q 121 = false := by
  rw [value23, value60, value63, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (104 : Vertex) (236 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 23 = false ∨ valuation q 70 = false ∨ valuation q 121 = false := by
  rw [value23, value60, value70, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (104 : Vertex) (248 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 55 = false ∨ valuation q 61 = false ∨ valuation q 70 = false := by
  rw [value55, value60, value61, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (233 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 55 = false ∨ valuation q 61 = false ∨ valuation q 121 = false := by
  rw [value55, value60, value61, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (233 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 70 = false := by
  rw [value60, value61, value63, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (233 : Vertex) (236 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 121 = false := by
  rw [value60, value61, value63, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (233 : Vertex) (236 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 70 = false ∨ valuation q 121 = false := by
  rw [value60, value61, value70, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (233 : Vertex) (248 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 63 = false ∨ valuation q 70 = false ∨ valuation q 121 = false := by
  rw [value60, value63, value70, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (236 : Vertex) (248 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 187 = true ∨ valuation q 23 = true ∨ valuation q 55 = true ∨ valuation q 61 = true ∨ valuation q 63 = true ∨ valuation q 121 = true := by
  rw [value23, value55, value60, value61, value63, value121, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(104 : Vertex), (224 : Vertex), (233 : Vertex), (236 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (248 : Vertex) [(104 : Vertex), (224 : Vertex), (233 : Vertex), (236 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 187 = true ∨ valuation q 23 = true ∨ valuation q 55 = true ∨ valuation q 61 = true ∨ valuation q 63 = true ∨ valuation q 70 = true := by
  rw [value23, value55, value60, value61, value63, value70, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(104 : Vertex), (224 : Vertex), (233 : Vertex), (236 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (488 : Vertex) [(104 : Vertex), (224 : Vertex), (233 : Vertex), (236 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 24 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value24, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (105 : Vertex) (232 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 24 = false ∨ valuation q 60 = false ∨ valuation q 64 = false := by
  rw [value24, value60, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (105 : Vertex) (232 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 24 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value24, value61, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (105 : Vertex) (235 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 60 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value60, value61, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (232 : Vertex) (235 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 188 = true ∨ valuation q 60 = true ∨ valuation q 62 = true ∨ valuation q 64 = true := by
  rw [value60, value61, value62, value64, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(232 : Vertex), (235 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (105 : Vertex) [(232 : Vertex), (235 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 62 = true := by
  rw [value62, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (235 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 25 = false ∨ valuation q 43 = false ∨ valuation q 57 = false := by
  rw [value25, value43, value57, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (203 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 25 = false ∨ valuation q 43 = false ∨ valuation q 71 = false := by
  rw [value25, value43, value62, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (203 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 25 = false ∨ valuation q 57 = false ∨ valuation q 61 = false := by
  rw [value25, value57, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (227 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 25 = false ∨ valuation q 57 = false ∨ valuation q 123 = false := by
  rw [value25, value57, value62, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (227 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 25 = false ∨ valuation q 61 = false ∨ valuation q 71 = false := by
  rw [value25, value61, value62, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (233 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 43 = false ∨ valuation q 61 = false ∨ valuation q 71 = false := by
  rw [value43, value61, value62, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (203 : Vertex) (233 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E260.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112260
