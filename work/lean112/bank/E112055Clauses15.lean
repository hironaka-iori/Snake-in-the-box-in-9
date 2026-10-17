import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 74 = false ∨ valuation q 90 = false ∨ valuation q 114 = false := by
  rw [value74, value77, value90, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (264 : Vertex) (284 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 74 = false ∨ valuation q 97 = false ∨ valuation q 114 = false := by
  rw [value74, value77, value97, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (264 : Vertex) (332 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 90 = false ∨ valuation q 97 = false := by
  rw [value77, value78, value90, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (269 : Vertex) (284 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 90 = false ∨ valuation q 97 = false ∨ valuation q 114 = false := by
  rw [value77, value90, value97, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (284 : Vertex) (332 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 205 = true ∨ valuation q 7 = true ∨ valuation q 70 = true ∨ valuation q 74 = true ∨ valuation q 78 = true ∨ valuation q 97 = true ∨ valuation q 114 = true := by
  rw [value7, value70, value74, value77, value78, value97, value114, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(12 : Vertex), (260 : Vertex), (264 : Vertex), (269 : Vertex), (332 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (284 : Vertex) [(12 : Vertex), (260 : Vertex), (264 : Vertex), (269 : Vertex), (332 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 71 = false ∨ valuation q 75 = false ∨ valuation q 77 = false := by
  rw [value71, value75, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (265 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 71 = false ∨ valuation q 75 = false ∨ valuation q 79 = false := by
  rw [value71, value75, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (265 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 71 = false ∨ valuation q 75 = false ∨ valuation q 98 = false := by
  rw [value71, value75, value78, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (265 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 71 = false ∨ valuation q 75 = false ∨ valuation q 115 = false := by
  rw [value71, value75, value78, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (265 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 71 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value71, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (268 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 71 = false ∨ valuation q 77 = false ∨ valuation q 98 = false := by
  rw [value71, value77, value78, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (268 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 71 = false ∨ valuation q 77 = false ∨ valuation q 115 = false := by
  rw [value71, value77, value78, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (268 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 71 = false ∨ valuation q 79 = false ∨ valuation q 98 = false := by
  rw [value71, value78, value79, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (271 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 71 = false ∨ valuation q 79 = false ∨ valuation q 115 = false := by
  rw [value71, value78, value79, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (271 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 71 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value71, value78, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (333 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value75, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (268 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 98 = false := by
  rw [value75, value77, value78, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (268 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 115 = false := by
  rw [value75, value77, value78, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (268 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 75 = false ∨ valuation q 79 = false ∨ valuation q 98 = false := by
  rw [value75, value78, value79, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (271 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 75 = false ∨ valuation q 79 = false ∨ valuation q 115 = false := by
  rw [value75, value78, value79, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (271 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 75 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value75, value78, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (333 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 77 = false ∨ valuation q 79 = false ∨ valuation q 98 = false := by
  rw [value77, value78, value79, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (268 : Vertex) (271 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 77 = false ∨ valuation q 79 = false ∨ valuation q 115 = false := by
  rw [value77, value78, value79, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (268 : Vertex) (271 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 77 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value77, value78, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (268 : Vertex) (333 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 206 = true ∨ valuation q 71 = true ∨ valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 98 = true := by
  rw [value71, value75, value77, value78, value79, value98, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (269 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(261 : Vertex), (265 : Vertex), (268 : Vertex), (271 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (269 : Vertex) (397 : Vertex) [(261 : Vertex), (265 : Vertex), (268 : Vertex), (271 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 9 = false ∨ valuation q 73 = false ∨ valuation q 78 = false := by
  rw [value9, value73, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 73 = false ∨ valuation q 78 = false ∨ valuation q 91 = false := by
  rw [value73, value78, value79, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (269 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 207 = true ∨ valuation q 73 = true ∨ valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 91 = true ∨ valuation q 117 = true := by
  rw [value73, value76, value78, value79, value91, value117, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(263 : Vertex), (267 : Vertex), (269 : Vertex), (287 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (15 : Vertex) [(263 : Vertex), (267 : Vertex), (269 : Vertex), (287 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 207 = true ∨ valuation q 9 = true ∨ valuation q 73 = true ∨ valuation q 78 = true ∨ valuation q 91 = true ∨ valuation q 117 = true := by
  rw [value9, value73, value78, value79, value91, value117, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(15 : Vertex), (263 : Vertex), (269 : Vertex), (287 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (267 : Vertex) [(15 : Vertex), (263 : Vertex), (269 : Vertex), (287 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 207 = true ∨ valuation q 9 = true ∨ valuation q 73 = true ∨ valuation q 76 = true ∨ valuation q 91 = true ∨ valuation q 117 = true := by
  rw [value9, value73, value76, value79, value91, value117, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(15 : Vertex), (263 : Vertex), (267 : Vertex), (287 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (269 : Vertex) [(15 : Vertex), (263 : Vertex), (267 : Vertex), (287 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 207 = true ∨ valuation q 9 = true ∨ valuation q 73 = true ∨ valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 91 = true := by
  rw [value9, value73, value76, value78, value79, value91, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(15 : Vertex), (263 : Vertex), (267 : Vertex), (269 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (399 : Vertex) [(15 : Vertex), (263 : Vertex), (267 : Vertex), (269 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 86 = false := by
  rw [value80, value81, value82, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (274 : Vertex) (276 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E055.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112055
