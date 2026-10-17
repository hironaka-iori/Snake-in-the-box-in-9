import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 77 = false ∨ valuation q 95 = false := by
  rw [value70, value72, value77, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (263 : Vertex) (269 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 77 = false ∨ valuation q 112 = false := by
  rw [value70, value72, value77, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (263 : Vertex) (269 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 82 = false ∨ valuation q 95 = false := by
  rw [value70, value72, value82, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (263 : Vertex) (277 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 82 = false ∨ valuation q 112 = false := by
  rw [value70, value72, value82, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (263 : Vertex) (277 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 95 = false ∨ valuation q 112 = false := by
  rw [value70, value72, value95, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (263 : Vertex) (325 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 77 = false ∨ valuation q 82 = false ∨ valuation q 95 = false := by
  rw [value70, value77, value82, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (269 : Vertex) (277 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 77 = false ∨ valuation q 82 = false ∨ valuation q 112 = false := by
  rw [value70, value77, value82, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (269 : Vertex) (277 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 77 = false ∨ valuation q 95 = false ∨ valuation q 112 = false := by
  rw [value70, value77, value95, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (269 : Vertex) (325 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 82 = false ∨ valuation q 95 = false ∨ valuation q 112 = false := by
  rw [value70, value82, value95, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (277 : Vertex) (325 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value69, value72, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (261 : Vertex) (260 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 71 = true := by
  rw [value71, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (262 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 83 = false := by
  rw [value69, value71, value72, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (260 : Vertex) (263 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value69, value72, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (262 : Vertex) (260 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 72 = false ∨ valuation q 83 = false := by
  rw [value72, value83, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (262 : Vertex) (263 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 198 = true ∨ valuation q 72 = true ∨ valuation q 83 = true := by
  rw [value71, value72, value83, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(263 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (260 : Vertex) [(263 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 198 = true ∨ valuation q 69 = true ∨ valuation q 83 = true := by
  rw [value69, value71, value83, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(260 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (263 : Vertex) [(260 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 198 = true ∨ valuation q 69 = true ∨ valuation q 72 = true := by
  rw [value69, value71, value72, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(260 : Vertex), (263 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (278 : Vertex) [(260 : Vertex), (263 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value68, value70, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (259 : Vertex) (261 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 84 = false := by
  rw [value68, value70, value72, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (259 : Vertex) (261 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 68 = false ∨ valuation q 71 = false ∨ valuation q 84 = false := by
  rw [value68, value71, value72, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (259 : Vertex) (262 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 78 = false := by
  rw [value70, value71, value72, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (262 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 70 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value70, value72, value78, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (271 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 71 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value71, value72, value78, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (271 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 199 = true ∨ valuation q 70 = true ∨ valuation q 71 = true ∨ valuation q 78 = true ∨ valuation q 84 = true := by
  rw [value70, value71, value72, value78, value84, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex), (271 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (259 : Vertex) [(261 : Vertex), (262 : Vertex), (271 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 199 = true ∨ valuation q 68 = true ∨ valuation q 70 = true ∨ valuation q 78 = true ∨ valuation q 84 = true := by
  rw [value68, value70, value72, value78, value84, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(259 : Vertex), (261 : Vertex), (271 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (262 : Vertex) [(259 : Vertex), (261 : Vertex), (271 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 199 = true ∨ valuation q 68 = true ∨ valuation q 70 = true ∨ valuation q 71 = true ∨ valuation q 84 = true := by
  rw [value68, value70, value71, value72, value84, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(259 : Vertex), (261 : Vertex), (262 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (271 : Vertex) [(259 : Vertex), (261 : Vertex), (262 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 199 = true ∨ valuation q 68 = true ∨ valuation q 70 = true ∨ valuation q 71 = true ∨ valuation q 78 = true := by
  rw [value68, value70, value71, value72, value78, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(259 : Vertex), (261 : Vertex), (262 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (279 : Vertex) [(259 : Vertex), (261 : Vertex), (262 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 5 = false ∨ valuation q 74 = false ∨ valuation q 76 = false := by
  rw [value5, value73, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (265 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 5 = false ∨ valuation q 74 = false ∨ valuation q 85 = false := by
  rw [value5, value73, value74, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (265 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 85 = false := by
  rw [value73, value74, value76, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (265 : Vertex) (268 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 200 = true ∨ valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 85 = true := by
  rw [value73, value74, value76, value85, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(265 : Vertex), (268 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (8 : Vertex) [(265 : Vertex), (268 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 200 = true ∨ valuation q 5 = true ∨ valuation q 76 = true ∨ valuation q 85 = true := by
  rw [value5, value73, value76, value85, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(8 : Vertex), (268 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (265 : Vertex) [(8 : Vertex), (268 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block15 (q : Snake 81) (h : Conditions q) : B112E057.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112057
