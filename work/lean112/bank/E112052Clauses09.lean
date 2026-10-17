import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 192 = true ∨ valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 106 = true := by
  rw [value64, value65, value66, value106, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(284 : Vertex), (287 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (270 : Vertex) [(284 : Vertex), (287 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 192 = true ∨ valuation q 58 = true ∨ valuation q 66 = true ∨ valuation q 106 = true := by
  rw [value58, value65, value66, value106, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(270 : Vertex), (287 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (284 : Vertex) [(270 : Vertex), (287 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 192 = true ∨ valuation q 58 = true ∨ valuation q 64 = true ∨ valuation q 106 = true := by
  rw [value58, value64, value65, value106, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(270 : Vertex), (284 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (287 : Vertex) [(270 : Vertex), (284 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 192 = true ∨ valuation q 58 = true ∨ valuation q 64 = true ∨ valuation q 66 = true := by
  rw [value58, value64, value65, value66, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(270 : Vertex), (284 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (414 : Vertex) [(270 : Vertex), (284 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 84 = false := by
  rw [value62, value65, value66, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (286 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 107 = false := by
  rw [value62, value65, value66, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (286 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 62 = false ∨ valuation q 84 = false ∨ valuation q 107 = false := by
  rw [value62, value66, value84, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (351 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 65 = false ∨ valuation q 84 = false ∨ valuation q 107 = false := by
  rw [value65, value66, value84, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (286 : Vertex) (351 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 193 = true ∨ valuation q 65 = true ∨ valuation q 84 = true ∨ valuation q 107 = true := by
  rw [value65, value66, value84, value107, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(286 : Vertex), (351 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (279 : Vertex) [(286 : Vertex), (351 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 193 = true ∨ valuation q 62 = true ∨ valuation q 84 = true ∨ valuation q 107 = true := by
  rw [value62, value66, value84, value107, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (286 : Vertex) → w ∈ [(279 : Vertex), (351 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (286 : Vertex) [(279 : Vertex), (351 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 2 = false ∨ valuation q 50 = false ∨ valuation q 70 = false := by
  rw [value2, value50, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (66 : Vertex) (258 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 2 = false ∨ valuation q 50 = false ∨ valuation q 73 = false := by
  rw [value2, value50, value67, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (66 : Vertex) (258 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 2 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value2, value67, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (66 : Vertex) (326 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 50 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value50, value67, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (326 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 194 = true ∨ valuation q 50 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value50, value67, value70, value73, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(258 : Vertex), (326 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (66 : Vertex) [(258 : Vertex), (326 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 194 = true ∨ valuation q 2 = true ∨ valuation q 50 = true ∨ valuation q 73 = true := by
  rw [value2, value50, value67, value73, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(66 : Vertex), (258 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (326 : Vertex) [(66 : Vertex), (258 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 194 = true ∨ valuation q 2 = true ∨ valuation q 50 = true ∨ valuation q 70 = true := by
  rw [value2, value50, value67, value70, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(66 : Vertex), (258 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (330 : Vertex) [(66 : Vertex), (258 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 52 = false ∨ valuation q 74 = false ∨ valuation q 111 = false := by
  rw [value52, value68, value74, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (260 : Vertex) (332 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 52 = false ∨ valuation q 76 = false ∨ valuation q 111 = false := by
  rw [value52, value68, value76, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (260 : Vertex) (340 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 74 = false := by
  rw [value68, value69, value70, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (325 : Vertex) (326 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 74 = false ∨ valuation q 76 = false := by
  rw [value68, value69, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (325 : Vertex) (332 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 76 = false := by
  rw [value68, value70, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (326 : Vertex) (332 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 111 = false := by
  rw [value68, value70, value74, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (326 : Vertex) (332 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 111 = false := by
  rw [value68, value74, value76, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (332 : Vertex) (340 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 195 = true ∨ valuation q 52 = true ∨ valuation q 69 = true ∨ valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 111 = true := by
  rw [value52, value68, value69, value74, value76, value111, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(260 : Vertex), (325 : Vertex), (332 : Vertex), (340 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (326 : Vertex) [(260 : Vertex), (325 : Vertex), (332 : Vertex), (340 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 195 = true ∨ valuation q 52 = true ∨ valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 76 = true ∨ valuation q 111 = true := by
  rw [value52, value68, value69, value70, value76, value111, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(260 : Vertex), (325 : Vertex), (326 : Vertex), (340 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (332 : Vertex) [(260 : Vertex), (325 : Vertex), (326 : Vertex), (340 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 195 = true ∨ valuation q 52 = true ∨ valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 74 = true ∨ valuation q 111 = true := by
  rw [value52, value68, value69, value70, value74, value111, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(260 : Vertex), (325 : Vertex), (326 : Vertex), (332 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (340 : Vertex) [(260 : Vertex), (325 : Vertex), (326 : Vertex), (332 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 195 = true ∨ valuation q 52 = true ∨ valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 74 = true ∨ valuation q 76 = true := by
  rw [value52, value68, value69, value70, value74, value76, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(260 : Vertex), (325 : Vertex), (326 : Vertex), (332 : Vertex), (340 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (452 : Vertex) [(260 : Vertex), (325 : Vertex), (326 : Vertex), (332 : Vertex), (340 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 53 = false ∨ valuation q 68 = false ∨ valuation q 71 = false := by
  rw [value53, value68, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (324 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 53 = false ∨ valuation q 68 = false ∨ valuation q 77 = false := by
  rw [value53, value68, value69, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (324 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 53 = false ∨ valuation q 68 = false ∨ valuation q 112 = false := by
  rw [value53, value68, value69, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (324 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 53 = false ∨ valuation q 71 = false ∨ valuation q 77 = false := by
  rw [value53, value69, value71, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (327 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E052.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112052
