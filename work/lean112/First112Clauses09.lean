import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 76 = true := by
  rw [value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 199 = true ∨ valuation q 78 = true := by
  rw [value77, value78, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(373 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (356 : Vertex) [(373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 78 = true := by
  rw [value78, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (373 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 77 = true ∨ valuation q 79 = true := by
  rw [value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ∈ [(372 : Vertex), (375 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (373 : Vertex) [(372 : Vertex), (375 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value77, value79, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (373 : Vertex) (372 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 200 = true ∨ valuation q 79 = true := by
  rw [value78, value79, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (372 : Vertex) → w ∈ [(375 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (372 : Vertex) [(375 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 200 = true ∨ valuation q 77 = true := by
  rw [value77, value78, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (375 : Vertex) → w ∈ [(372 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (375 : Vertex) [(372 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 201 = true ∨ valuation q 78 = true := by
  rw [value78, value79, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(373 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (359 : Vertex) [(373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 201 = true ∨ valuation q 75 = true := by
  rw [value75, value79, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(359 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (373 : Vertex) [(359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 81 = false := by
  rw [value20, value55, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (288 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 87 = false := by
  rw [value20, value55, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (288 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 55 = false ∨ valuation q 81 = false ∨ valuation q 87 = false := by
  rw [value55, value80, value81, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (417 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 55 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value55, value80, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (418 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 55 = false ∨ valuation q 83 = false ∨ valuation q 87 = false := by
  rw [value55, value80, value83, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (420 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 55 = false ∨ valuation q 83 = false ∨ valuation q 103 = false := by
  rw [value55, value80, value83, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (420 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 55 = false ∨ valuation q 87 = false ∨ valuation q 103 = false := by
  rw [value55, value80, value87, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (424 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 87 = false := by
  rw [value80, value81, value83, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (420 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 87 = false ∨ valuation q 103 = false := by
  rw [value80, value81, value87, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (424 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 83 = false ∨ valuation q 87 = false ∨ valuation q 103 = false := by
  rw [value80, value83, value87, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (420 : Vertex) (424 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 202 = true ∨ valuation q 55 = true ∨ valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 83 = true ∨ valuation q 87 = true ∨ valuation q 103 = true := by
  rw [value55, value80, value81, value82, value83, value87, value103, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(288 : Vertex), (417 : Vertex), (418 : Vertex), (420 : Vertex), (424 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (160 : Vertex) [(288 : Vertex), (417 : Vertex), (418 : Vertex), (420 : Vertex), (424 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 21 = false ∨ valuation q 56 = false ∨ valuation q 80 = false := by
  rw [value21, value56, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 21 = false ∨ valuation q 56 = false ∨ valuation q 84 = false := by
  rw [value21, value56, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 21 = false ∨ valuation q 56 = false ∨ valuation q 93 = false := by
  rw [value21, value56, value81, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 21 = false ∨ valuation q 56 = false ∨ valuation q 104 = false := by
  rw [value21, value56, value81, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 21 = false ∨ valuation q 80 = false ∨ valuation q 84 = false := by
  rw [value21, value80, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (416 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 21 = false ∨ valuation q 80 = false ∨ valuation q 93 = false := by
  rw [value21, value80, value81, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (416 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 21 = false ∨ valuation q 80 = false ∨ valuation q 104 = false := by
  rw [value21, value80, value81, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (416 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 21 = false ∨ valuation q 84 = false ∨ valuation q 93 = false := by
  rw [value21, value81, value84, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 21 = false ∨ valuation q 84 = false ∨ valuation q 104 = false := by
  rw [value21, value81, value84, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 21 = false ∨ valuation q 93 = false ∨ valuation q 104 = false := by
  rw [value21, value81, value93, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 56 = false ∨ valuation q 80 = false ∨ valuation q 84 = false := by
  rw [value56, value80, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (416 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 56 = false ∨ valuation q 80 = false ∨ valuation q 93 = false := by
  rw [value56, value80, value81, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (416 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.First112
