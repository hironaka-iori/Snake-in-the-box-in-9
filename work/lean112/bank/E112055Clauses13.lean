import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 199 = true ∨ valuation q 70 = true ∨ valuation q 73 = true ∨ valuation q 78 = true ∨ valuation q 83 = true ∨ valuation q 95 = true ∨ valuation q 112 = true := by
  rw [value70, value71, value73, value78, value83, value95, value112, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (5 : Vertex) → w ∈ [(260 : Vertex), (263 : Vertex), (269 : Vertex), (277 : Vertex), (325 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (5 : Vertex) [(260 : Vertex), (263 : Vertex), (269 : Vertex), (277 : Vertex), (325 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 199 = true ∨ valuation q 4 = true ∨ valuation q 73 = true ∨ valuation q 78 = true ∨ valuation q 83 = true ∨ valuation q 95 = true ∨ valuation q 112 = true := by
  rw [value4, value71, value73, value78, value83, value95, value112, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(5 : Vertex), (263 : Vertex), (269 : Vertex), (277 : Vertex), (325 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (260 : Vertex) [(5 : Vertex), (263 : Vertex), (269 : Vertex), (277 : Vertex), (325 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 199 = true ∨ valuation q 4 = true ∨ valuation q 70 = true ∨ valuation q 73 = true ∨ valuation q 78 = true ∨ valuation q 83 = true ∨ valuation q 112 = true := by
  rw [value4, value70, value71, value73, value78, value83, value112, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(5 : Vertex), (260 : Vertex), (263 : Vertex), (269 : Vertex), (277 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (325 : Vertex) [(5 : Vertex), (260 : Vertex), (263 : Vertex), (269 : Vertex), (277 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 199 = true ∨ valuation q 4 = true ∨ valuation q 70 = true ∨ valuation q 73 = true ∨ valuation q 78 = true ∨ valuation q 83 = true ∨ valuation q 95 = true := by
  rw [value4, value70, value71, value73, value78, value83, value95, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(5 : Vertex), (260 : Vertex), (263 : Vertex), (269 : Vertex), (277 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (389 : Vertex) [(5 : Vertex), (260 : Vertex), (263 : Vertex), (269 : Vertex), (277 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 72 = true := by
  rw [value72, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (262 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 70 = true ∨ valuation q 73 = true ∨ valuation q 84 = true := by
  rw [value70, value72, value73, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ∈ [(260 : Vertex), (263 : Vertex), (278 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (262 : Vertex) [(260 : Vertex), (263 : Vertex), (278 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value70, value73, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (262 : Vertex) (260 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 73 = false ∨ valuation q 84 = false := by
  rw [value73, value84, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (262 : Vertex) (263 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 73 = true ∨ valuation q 84 = true := by
  rw [value72, value73, value84, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(263 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (260 : Vertex) [(263 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 70 = true ∨ valuation q 84 = true := by
  rw [value70, value72, value84, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(260 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (263 : Vertex) [(260 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value70, value72, value73, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(260 : Vertex), (263 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (278 : Vertex) [(260 : Vertex), (263 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value69, value71, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (259 : Vertex) (261 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 79 = false := by
  rw [value69, value71, value73, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (259 : Vertex) (261 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 85 = false := by
  rw [value69, value71, value73, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (259 : Vertex) (261 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 79 = false := by
  rw [value69, value72, value73, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (259 : Vertex) (262 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 85 = false := by
  rw [value69, value72, value73, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (259 : Vertex) (262 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 69 = false ∨ valuation q 79 = false ∨ valuation q 85 = false := by
  rw [value69, value73, value79, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (259 : Vertex) (271 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 79 = false := by
  rw [value71, value72, value73, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (262 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 85 = false := by
  rw [value71, value72, value73, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (262 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 71 = false ∨ valuation q 79 = false ∨ valuation q 85 = false := by
  rw [value71, value73, value79, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (271 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 72 = false ∨ valuation q 79 = false ∨ valuation q 85 = false := by
  rw [value72, value73, value79, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (271 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 201 = true ∨ valuation q 71 = true ∨ valuation q 72 = true ∨ valuation q 79 = true ∨ valuation q 85 = true := by
  rw [value71, value72, value73, value79, value85, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex), (271 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (259 : Vertex) [(261 : Vertex), (262 : Vertex), (271 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 201 = true ∨ valuation q 69 = true ∨ valuation q 71 = true ∨ valuation q 79 = true ∨ valuation q 85 = true := by
  rw [value69, value71, value73, value79, value85, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(259 : Vertex), (261 : Vertex), (271 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (262 : Vertex) [(259 : Vertex), (261 : Vertex), (271 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 201 = true ∨ valuation q 69 = true ∨ valuation q 71 = true ∨ valuation q 72 = true ∨ valuation q 85 = true := by
  rw [value69, value71, value72, value73, value85, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(259 : Vertex), (261 : Vertex), (262 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (271 : Vertex) [(259 : Vertex), (261 : Vertex), (262 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 5 = false ∨ valuation q 75 = false ∨ valuation q 77 = false := by
  rw [value5, value74, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (265 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 5 = false ∨ valuation q 75 = false ∨ valuation q 86 = false := by
  rw [value5, value74, value75, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (265 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 5 = false ∨ valuation q 77 = false ∨ valuation q 86 = false := by
  rw [value5, value74, value77, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (268 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 86 = false := by
  rw [value74, value75, value77, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (265 : Vertex) (268 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 202 = true ∨ valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 86 = true := by
  rw [value74, value75, value77, value86, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(265 : Vertex), (268 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (8 : Vertex) [(265 : Vertex), (268 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 202 = true ∨ valuation q 5 = true ∨ valuation q 77 = true ∨ valuation q 86 = true := by
  rw [value5, value74, value77, value86, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(8 : Vertex), (268 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (265 : Vertex) [(8 : Vertex), (268 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 202 = true ∨ valuation q 5 = true ∨ valuation q 75 = true ∨ valuation q 77 = true := by
  rw [value5, value74, value75, value77, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(8 : Vertex), (265 : Vertex), (268 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (280 : Vertex) [(8 : Vertex), (265 : Vertex), (268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 75 = true := by
  rw [value75, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (265 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem block13 (q : Snake 81) (h : Conditions q) : B112E055.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112055
