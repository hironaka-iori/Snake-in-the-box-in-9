import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 27 = false ∨ valuation q 55 = false ∨ valuation q 64 = false := by
  rw [value27, value55, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (112 : Vertex) (224 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 55 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value55, value63, value64, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (224 : Vertex) (241 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 55 = false ∨ valuation q 64 = false ∨ valuation q 69 = false := by
  rw [value55, value63, value64, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (224 : Vertex) (241 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 190 = true ∨ valuation q 27 = true ∨ valuation q 55 = true ∨ valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 69 = true := by
  rw [value27, value55, value63, value64, value66, value69, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (240 : Vertex) w → w ∈ region → w ≠ (496 : Vertex) → w ∈ [(112 : Vertex), (224 : Vertex), (241 : Vertex), (244 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (240 : Vertex) (496 : Vertex) [(112 : Vertex), (224 : Vertex), (241 : Vertex), (244 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 28 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value28, value63, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (113 : Vertex) (240 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 28 = false ∨ valuation q 63 = false ∨ valuation q 67 = false := by
  rw [value28, value63, value64, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (113 : Vertex) (240 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 28 = false ∨ valuation q 65 = false ∨ valuation q 67 = false := by
  rw [value28, value64, value65, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (113 : Vertex) (243 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 67 = false := by
  rw [value63, value64, value65, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (240 : Vertex) (243 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 191 = true ∨ valuation q 63 = true ∨ valuation q 65 = true ∨ valuation q 67 = true := by
  rw [value63, value64, value65, value67, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(240 : Vertex), (243 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (113 : Vertex) [(240 : Vertex), (243 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 191 = true ∨ valuation q 28 = true ∨ valuation q 65 = true ∨ valuation q 67 = true := by
  rw [value28, value64, value65, value67, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(113 : Vertex), (243 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (240 : Vertex) [(113 : Vertex), (243 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 191 = true ∨ valuation q 28 = true ∨ valuation q 63 = true ∨ valuation q 65 = true := by
  rw [value28, value63, value64, value65, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(113 : Vertex), (240 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (245 : Vertex) [(113 : Vertex), (240 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 65 = true := by
  rw [value65, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (243 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 29 = false ∨ valuation q 46 = false ∨ valuation q 56 = false := by
  rw [value29, value46, value56, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (211 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 29 = false ∨ valuation q 56 = false ∨ valuation q 64 = false := by
  rw [value29, value56, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (227 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 29 = false ∨ valuation q 56 = false ∨ valuation q 119 = false := by
  rw [value29, value56, value65, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (227 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 46 = false ∨ valuation q 56 = false ∨ valuation q 64 = false := by
  rw [value46, value56, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (211 : Vertex) (227 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 30 = false ∨ valuation q 47 = false ∨ valuation q 57 = false := by
  rw [value30, value47, value57, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (116 : Vertex) (212 : Vertex) (228 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 30 = false ∨ valuation q 47 = false ∨ valuation q 63 = false := by
  rw [value30, value47, value63, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (116 : Vertex) (212 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 30 = false ∨ valuation q 47 = false ∨ valuation q 67 = false := by
  rw [value30, value47, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (116 : Vertex) (212 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 30 = false ∨ valuation q 47 = false ∨ valuation q 68 = false := by
  rw [value30, value47, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (116 : Vertex) (212 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 30 = false ∨ valuation q 57 = false ∨ valuation q 63 = false := by
  rw [value30, value57, value63, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (116 : Vertex) (228 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 30 = false ∨ valuation q 57 = false ∨ valuation q 67 = false := by
  rw [value30, value57, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (116 : Vertex) (228 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 30 = false ∨ valuation q 57 = false ∨ valuation q 68 = false := by
  rw [value30, value57, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (116 : Vertex) (228 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 30 = false ∨ valuation q 57 = false ∨ valuation q 120 = false := by
  rw [value30, value57, value66, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (116 : Vertex) (228 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 30 = false ∨ valuation q 63 = false ∨ valuation q 67 = false := by
  rw [value30, value63, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (116 : Vertex) (240 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 30 = false ∨ valuation q 63 = false ∨ valuation q 68 = false := by
  rw [value30, value63, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (116 : Vertex) (240 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 30 = false ∨ valuation q 63 = false ∨ valuation q 120 = false := by
  rw [value30, value63, value66, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (116 : Vertex) (240 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 30 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value30, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (116 : Vertex) (245 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 30 = false ∨ valuation q 67 = false ∨ valuation q 120 = false := by
  rw [value30, value66, value67, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (116 : Vertex) (245 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 47 = false ∨ valuation q 57 = false ∨ valuation q 63 = false := by
  rw [value47, value57, value63, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (212 : Vertex) (228 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 47 = false ∨ valuation q 57 = false ∨ valuation q 67 = false := by
  rw [value47, value57, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (212 : Vertex) (228 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 47 = false ∨ valuation q 57 = false ∨ valuation q 68 = false := by
  rw [value47, value57, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (212 : Vertex) (228 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E256.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112256
