import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 62 = false ∨ valuation q 73 = false ∨ valuation q 112 = false := by
  rw [value62, value64, value73, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (204 : Vertex) (222 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 73 = false ∨ valuation q 112 = false := by
  rw [value64, value65, value73, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (207 : Vertex) (222 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 182 = true ∨ valuation q 63 = true ∨ valuation q 64 = true := by
  rw [value63, value64, value65, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(205 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (199 : Vertex) [(205 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 182 = true ∨ valuation q 60 = true ∨ valuation q 64 = true := by
  rw [value60, value64, value65, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(199 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (205 : Vertex) [(199 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 56 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value56, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (192 : Vertex) (209 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 56 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value56, value66, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (192 : Vertex) (209 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 56 = false ∨ valuation q 68 = false ∨ valuation q 70 = false := by
  rw [value56, value66, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (192 : Vertex) (210 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 70 = false := by
  rw [value66, value67, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (209 : Vertex) (210 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 183 = true ∨ valuation q 67 = true ∨ valuation q 68 = true ∨ valuation q 70 = true := by
  rw [value66, value67, value68, value70, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(209 : Vertex), (210 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (192 : Vertex) [(209 : Vertex), (210 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 183 = true ∨ valuation q 56 = true ∨ valuation q 68 = true ∨ valuation q 70 = true := by
  rw [value56, value66, value68, value70, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(192 : Vertex), (210 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (209 : Vertex) [(192 : Vertex), (210 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 184 = true ∨ valuation q 66 = true ∨ valuation q 69 = true := by
  rw [value66, value67, value69, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(208 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (193 : Vertex) [(208 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 184 = true ∨ valuation q 57 = true ∨ valuation q 69 = true := by
  rw [value57, value67, value69, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(193 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (208 : Vertex) [(193 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 184 = true ∨ valuation q 57 = true ∨ valuation q 66 = true := by
  rw [value57, value66, value67, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(193 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (211 : Vertex) [(193 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 31 = false ∨ valuation q 47 = false ∨ valuation q 71 = false := by
  rw [value31, value47, value68, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (82 : Vertex) (146 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 31 = false ∨ valuation q 58 = false ∨ valuation q 71 = false := by
  rw [value31, value58, value68, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (82 : Vertex) (194 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 47 = false ∨ valuation q 58 = false ∨ valuation q 71 = false := by
  rw [value47, value58, value68, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (146 : Vertex) (194 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 47 = false ∨ valuation q 66 = false ∨ valuation q 71 = false := by
  rw [value47, value66, value68, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (146 : Vertex) (208 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 58 = false ∨ valuation q 69 = false ∨ valuation q 71 = false := by
  rw [value58, value68, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (211 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 66 = false ∨ valuation q 69 = false ∨ valuation q 71 = false := by
  rw [value66, value68, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (208 : Vertex) (211 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 185 = true ∨ valuation q 31 = true ∨ valuation q 47 = true ∨ valuation q 58 = true ∨ valuation q 66 = true ∨ valuation q 69 = true := by
  rw [value31, value47, value58, value66, value68, value69, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(82 : Vertex), (146 : Vertex), (194 : Vertex), (208 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (218 : Vertex) [(82 : Vertex), (146 : Vertex), (194 : Vertex), (208 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 32 = false ∨ valuation q 48 = false ∨ valuation q 59 = false := by
  rw [value32, value48, value59, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (147 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 32 = false ∨ valuation q 48 = false ∨ valuation q 67 = false := by
  rw [value32, value48, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (147 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 32 = false ∨ valuation q 48 = false ∨ valuation q 68 = false := by
  rw [value32, value48, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (147 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 32 = false ∨ valuation q 59 = false ∨ valuation q 67 = false := by
  rw [value32, value59, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (195 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 32 = false ∨ valuation q 59 = false ∨ valuation q 68 = false := by
  rw [value32, value59, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (195 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 32 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value32, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (209 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 48 = false ∨ valuation q 59 = false ∨ valuation q 67 = false := by
  rw [value48, value59, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (147 : Vertex) (195 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 48 = false ∨ valuation q 59 = false ∨ valuation q 68 = false := by
  rw [value48, value59, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (147 : Vertex) (195 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 48 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value48, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (147 : Vertex) (209 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 59 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value59, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (195 : Vertex) (209 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 49 = false ∨ valuation q 66 = false ∨ valuation q 72 = false := by
  rw [value49, value66, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (148 : Vertex) (208 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 49 = false ∨ valuation q 66 = false ∨ valuation q 113 = false := by
  rw [value49, value66, value70, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (148 : Vertex) (208 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E115.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112115
