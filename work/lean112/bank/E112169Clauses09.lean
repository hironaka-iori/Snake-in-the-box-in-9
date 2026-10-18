import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 173 = true ∨ valuation q 60 = true := by
  rw [value57, value60, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(287 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (277 : Vertex) [(287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 173 = true ∨ valuation q 56 = true := by
  rw [value56, value57, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(277 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (287 : Vertex) [(277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 174 = true := by
  rw [value58, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (281 : Vertex) (283 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 59 = true := by
  rw [value59, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (283 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 53 = true ∨ valuation q 58 = true ∨ valuation q 60 = true := by
  rw [value53, value58, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ∈ [(267 : Vertex), (281 : Vertex), (287 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (283 : Vertex) [(267 : Vertex), (281 : Vertex), (287 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 53 = false ∨ valuation q 60 = false := by
  rw [value53, value60, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (283 : Vertex) (267 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 175 = true ∨ valuation q 58 = true ∨ valuation q 60 = true := by
  rw [value58, value59, value60, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(281 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (267 : Vertex) [(281 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 176 = true ∨ valuation q 59 = true := by
  rw [value59, value60, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(283 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (279 : Vertex) [(283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 176 = true ∨ valuation q 57 = true := by
  rw [value57, value60, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(279 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (283 : Vertex) [(279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 177 = true := by
  rw [value61, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (304 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (288 : Vertex) (304 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 51 = false ∨ valuation q 65 = false ∨ valuation q 67 = false := by
  rw [value51, value62, value65, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (291 : Vertex) (259 : Vertex) (307 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 51 = false ∨ valuation q 65 = false ∨ valuation q 83 = false := by
  rw [value51, value62, value65, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (291 : Vertex) (259 : Vertex) (307 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 51 = false ∨ valuation q 67 = false ∨ valuation q 83 = false := by
  rw [value51, value62, value67, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (291 : Vertex) (259 : Vertex) (355 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 83 = false := by
  rw [value62, value65, value67, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (291 : Vertex) (307 : Vertex) (355 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 179 = true ∨ valuation q 54 = true ∨ valuation q 61 = true ∨ valuation q 64 = true ∨ valuation q 90 = true := by
  rw [value54, value61, value63, value64, value90, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (304 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(272 : Vertex), (288 : Vertex), (305 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (304 : Vertex) (368 : Vertex) [(272 : Vertex), (288 : Vertex), (305 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 180 = true ∨ valuation q 65 = true := by
  rw [value64, value65, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (304 : Vertex) → w ∈ [(307 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (304 : Vertex) [(307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 181 = true ∨ valuation q 62 = true := by
  rw [value62, value65, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(291 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(291 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 182 = true ∨ valuation q 67 = true := by
  rw [value66, value67, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (354 : Vertex) w → w ∈ region → w ≠ (362 : Vertex) → w ∈ [(355 : Vertex)] := by decide
  have hg := other_cover q (354 : Vertex) (362 : Vertex) [(355 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 183 = true ∨ valuation q 62 = true ∨ valuation q 71 = true := by
  rw [value62, value67, value71, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (354 : Vertex) → w ∈ [(291 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (354 : Vertex) [(291 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value68, value69, value72, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (357 : Vertex) (364 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 68 = true ∨ valuation q 76 = true := by
  rw [value68, value69, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ∈ [(356 : Vertex), (373 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (357 : Vertex) [(356 : Vertex), (373 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 186 = true ∨ valuation q 66 = true ∨ valuation q 71 = true := by
  rw [value66, value70, value71, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(354 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (366 : Vertex) [(354 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 80 = false := by
  rw [value67, value70, value71, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 63 = false ∨ valuation q 75 = false ∨ valuation q 78 = false := by
  rw [value63, value74, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (304 : Vertex) (372 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 69 = false ∨ valuation q 75 = false ∨ valuation q 77 = false := by
  rw [value69, value75, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (357 : Vertex) (372 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 193 = true ∨ valuation q 81 = true := by
  rw [value77, value81, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(383 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (373 : Vertex) [(383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 194 = true ∨ valuation q 79 = true := by
  rw [value78, value79, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(377 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (368 : Vertex) [(377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 194 = true ∨ valuation q 74 = true := by
  rw [value74, value78, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(368 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (377 : Vertex) [(368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 71 = false ∨ valuation q 79 = false ∨ valuation q 81 = false := by
  rw [value71, value79, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (363 : Vertex) (377 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 13 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value13, value82, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (162 : Vertex) (419 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 198 = true ∨ valuation q 13 = true ∨ valuation q 83 = true := by
  rw [value13, value82, value83, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(162 : Vertex), (419 : Vertex)] := by decide
  have hg := other_cover q (418 : Vertex) (426 : Vertex) [(162 : Vertex), (419 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 14 = true ∨ valuation q 62 = true ∨ valuation q 82 = true ∨ valuation q 87 = true := by
  rw [value14, value62, value82, value83, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ∈ [(163 : Vertex), (291 : Vertex), (418 : Vertex), (427 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (419 : Vertex) [(163 : Vertex), (291 : Vertex), (418 : Vertex), (427 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block9 (q : Snake 81) (h : Conditions q) : B112E169.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112169
