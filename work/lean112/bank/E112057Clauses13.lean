import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 184 = true ∨ valuation q 56 = true := by
  rw [value56, value57, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(192 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (197 : Vertex) [(192 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 185 = true ∨ valuation q 60 = true := by
  rw [value58, value60, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(202 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (192 : Vertex) [(202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 185 = true ∨ valuation q 56 = true := by
  rw [value56, value58, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(192 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (202 : Vertex) [(192 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 23 = false ∨ valuation q 40 = false ∨ valuation q 66 = false := by
  rw [value23, value40, value59, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (133 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 23 = false ∨ valuation q 57 = false ∨ valuation q 66 = false := by
  rw [value23, value57, value59, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (193 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 40 = false ∨ valuation q 57 = false ∨ valuation q 66 = false := by
  rw [value40, value57, value59, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (133 : Vertex) (193 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 186 = true ∨ valuation q 23 = true ∨ valuation q 40 = true ∨ valuation q 57 = true := by
  rw [value23, value40, value57, value59, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (197 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(69 : Vertex), (133 : Vertex), (193 : Vertex)] := by decide
  have hg := other_cover q (197 : Vertex) (229 : Vertex) [(69 : Vertex), (133 : Vertex), (193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 45 = false ∨ valuation q 58 = false ∨ valuation q 62 = false := by
  rw [value45, value58, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (138 : Vertex) (194 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 187 = true ∨ valuation q 58 = true ∨ valuation q 62 = true := by
  rw [value58, value60, value62, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(194 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (138 : Vertex) [(194 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 187 = true ∨ valuation q 45 = true ∨ valuation q 62 = true := by
  rw [value45, value60, value62, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(138 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (194 : Vertex) [(138 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 187 = true ∨ valuation q 45 = true ∨ valuation q 58 = true := by
  rw [value45, value58, value60, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(138 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (206 : Vertex) [(138 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 188 = true := by
  rw [value61, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (204 : Vertex) (206 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 189 = true ∨ valuation q 61 = true ∨ valuation q 64 = true := by
  rw [value61, value62, value64, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(204 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (202 : Vertex) [(204 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 189 = true ∨ valuation q 60 = true ∨ valuation q 61 = true := by
  rw [value60, value61, value62, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(202 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (222 : Vertex) [(202 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 63 = true := by
  rw [value63, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (208 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 30 = false ∨ valuation q 48 = false ∨ valuation q 56 = false := by
  rw [value30, value48, value56, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (144 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 190 = true ∨ valuation q 30 = true ∨ valuation q 48 = true := by
  rw [value30, value48, value63, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(80 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (192 : Vertex) [(80 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 37 = false ∨ valuation q 55 = false ∨ valuation q 62 = false := by
  rw [value37, value55, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (158 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 191 = true ∨ valuation q 55 = true ∨ valuation q 62 = true := by
  rw [value55, value62, value64, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(158 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (94 : Vertex) [(158 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 191 = true ∨ valuation q 37 = true ∨ valuation q 62 = true := by
  rw [value37, value62, value64, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(94 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (158 : Vertex) [(94 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 191 = true ∨ valuation q 37 = true ∨ valuation q 55 = true := by
  rw [value37, value55, value64, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(94 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (206 : Vertex) [(94 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 192 = true := by
  rw [value65, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (228 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (228 : Vertex) (229 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 59 = false ∨ valuation q 127 = false := by
  rw [value59, value127, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (229 : Vertex) (197 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 193 = true ∨ valuation q 59 = true ∨ valuation q 65 = true ∨ valuation q 67 = true := by
  rw [value59, value65, value66, value67, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(197 : Vertex), (228 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (485 : Vertex) [(197 : Vertex), (228 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 194 = true := by
  rw [value67, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (245 : Vertex) (229 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 68 = true := by
  rw [value68, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (259 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 72 = true ∨ valuation q 75 = true ∨ valuation q 94 = true := by
  rw [value68, value72, value75, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ∈ [(263 : Vertex), (267 : Vertex), (323 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (259 : Vertex) [(263 : Vertex), (267 : Vertex), (323 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 72 = false ∨ valuation q 75 = false ∨ valuation q 94 = false := by
  rw [value68, value72, value75, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (259 : Vertex) (263 : Vertex) (267 : Vertex) (323 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value72, value75, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (259 : Vertex) (263 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 195 = true ∨ valuation q 75 = true ∨ valuation q 94 = true := by
  rw [value68, value75, value94, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(267 : Vertex), (323 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (263 : Vertex) [(267 : Vertex), (323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 195 = true ∨ valuation q 72 = true ∨ valuation q 94 = true := by
  rw [value68, value72, value94, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(263 : Vertex), (323 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (267 : Vertex) [(263 : Vertex), (323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 76 = false ∨ valuation q 81 = false := by
  rw [value69, value71, value76, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (262 : Vertex) (268 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E057.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112057
