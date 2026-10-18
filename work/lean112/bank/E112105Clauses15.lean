import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 84 = true ∨ valuation q 87 = true ∨ valuation q 104 = true := by
  rw [value84, value85, value87, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ∈ [(384 : Vertex), (390 : Vertex), (450 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (386 : Vertex) [(384 : Vertex), (390 : Vertex), (450 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 84 = false ∨ valuation q 87 = false ∨ valuation q 104 = false := by
  rw [value84, value85, value87, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (384 : Vertex) (390 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value84, value87, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (386 : Vertex) (384 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 84 = false ∨ valuation q 104 = false := by
  rw [value84, value104, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (386 : Vertex) (384 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 87 = false ∨ valuation q 104 = false := by
  rw [value87, value104, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (386 : Vertex) (390 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 209 = true ∨ valuation q 87 = true ∨ valuation q 104 = true := by
  rw [value85, value87, value104, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(390 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (384 : Vertex) [(390 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 209 = true ∨ valuation q 84 = true ∨ valuation q 104 = true := by
  rw [value84, value85, value104, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(384 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (390 : Vertex) [(384 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 209 = true ∨ valuation q 84 = true ∨ valuation q 87 = true := by
  rw [value84, value85, value87, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(384 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (450 : Vertex) [(384 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 33 = false ∨ valuation q 88 = false ∨ valuation q 95 = false := by
  rw [value33, value86, value88, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (391 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 33 = false ∨ valuation q 95 = false ∨ valuation q 106 = false := by
  rw [value33, value86, value95, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (405 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 95 = false ∨ valuation q 106 = false := by
  rw [value86, value88, value95, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (391 : Vertex) (405 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 210 = true ∨ valuation q 33 = true ∨ valuation q 88 = true ∨ valuation q 106 = true := by
  rw [value33, value86, value88, value106, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(133 : Vertex), (391 : Vertex), (453 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (405 : Vertex) [(133 : Vertex), (391 : Vertex), (453 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value85, value87, value88, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (391 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 107 = false := by
  rw [value85, value87, value88, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (391 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 91 = false ∨ valuation q 107 = false := by
  rw [value85, value87, value91, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (398 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 107 = false := by
  rw [value87, value88, value91, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (391 : Vertex) (398 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 211 = true ∨ valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 107 = true := by
  rw [value87, value88, value91, value107, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(391 : Vertex), (398 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (386 : Vertex) [(391 : Vertex), (398 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 211 = true ∨ valuation q 85 = true ∨ valuation q 91 = true ∨ valuation q 107 = true := by
  rw [value85, value87, value91, value107, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(386 : Vertex), (398 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (391 : Vertex) [(386 : Vertex), (398 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 211 = true ∨ valuation q 85 = true ∨ valuation q 88 = true ∨ valuation q 107 = true := by
  rw [value85, value87, value88, value107, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(386 : Vertex), (391 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (398 : Vertex) [(386 : Vertex), (391 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 34 = false ∨ valuation q 87 = false ∨ valuation q 96 = false := by
  rw [value34, value87, value88, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (135 : Vertex) (390 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 34 = false ∨ valuation q 92 = false ∨ valuation q 96 = false := by
  rw [value34, value88, value92, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (135 : Vertex) (399 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 212 = true ∨ valuation q 86 = true ∨ valuation q 87 = true ∨ valuation q 92 = true ∨ valuation q 96 = true := by
  rw [value86, value87, value88, value92, value96, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(389 : Vertex), (390 : Vertex), (399 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (135 : Vertex) [(389 : Vertex), (390 : Vertex), (399 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 89 = true := by
  rw [value89, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (392 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 84 = false ∨ valuation q 90 = false ∨ valuation q 97 = false := by
  rw [value84, value89, value90, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (384 : Vertex) (393 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 213 = true ∨ valuation q 90 = true ∨ valuation q 97 = true := by
  rw [value89, value90, value97, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(393 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (384 : Vertex) [(393 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 213 = true ∨ valuation q 84 = true ∨ valuation q 97 = true := by
  rw [value84, value89, value97, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(384 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (393 : Vertex) [(384 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 213 = true ∨ valuation q 84 = true ∨ valuation q 90 = true := by
  rw [value84, value89, value90, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (408 : Vertex) [(384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 35 = false ∨ valuation q 89 = false ∨ valuation q 98 = false := by
  rw [value35, value89, value90, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (392 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 35 = false ∨ valuation q 89 = false ∨ valuation q 108 = false := by
  rw [value35, value89, value90, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (392 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 35 = false ∨ valuation q 98 = false ∨ valuation q 108 = false := by
  rw [value35, value90, value98, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (409 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 108 = false := by
  rw [value89, value90, value98, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (392 : Vertex) (409 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 214 = true ∨ valuation q 89 = true ∨ valuation q 98 = true ∨ valuation q 108 = true := by
  rw [value89, value90, value98, value108, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (393 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(392 : Vertex), (409 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (393 : Vertex) (137 : Vertex) [(392 : Vertex), (409 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block15 (q : Snake 81) (h : Conditions q) : B112E105.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112105
