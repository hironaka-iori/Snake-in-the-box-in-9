import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 27 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value27, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (177 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 27 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value27, value86, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (178 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 75 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value75, value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (177 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 75 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value75, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (177 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 75 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value75, value86, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (178 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value86, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 27 = false ∨ valuation q 89 = false := by
  rw [value27, value89, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (176 : Vertex) (48 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 202 = true ∨ valuation q 75 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 89 = true := by
  rw [value75, value86, value87, value88, value89, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(160 : Vertex), (177 : Vertex), (178 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (48 : Vertex) [(160 : Vertex), (177 : Vertex), (178 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 202 = true ∨ valuation q 27 = true ∨ valuation q 75 = true ∨ valuation q 87 = true ∨ valuation q 89 = true := by
  rw [value27, value75, value86, value87, value89, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(48 : Vertex), (160 : Vertex), (177 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (178 : Vertex) [(48 : Vertex), (160 : Vertex), (177 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 202 = true ∨ valuation q 27 = true ∨ valuation q 75 = true ∨ valuation q 87 = true ∨ valuation q 88 = true := by
  rw [value27, value75, value86, value87, value88, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(48 : Vertex), (160 : Vertex), (177 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (180 : Vertex) [(48 : Vertex), (160 : Vertex), (177 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 28 = false ∨ valuation q 76 = false ∨ valuation q 86 = false := by
  rw [value28, value76, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (49 : Vertex) (161 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 28 = false ∨ valuation q 76 = false ∨ valuation q 90 = false := by
  rw [value28, value76, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (49 : Vertex) (161 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 28 = false ∨ valuation q 76 = false ∨ valuation q 92 = false := by
  rw [value28, value76, value87, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (49 : Vertex) (161 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 28 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value28, value86, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (49 : Vertex) (176 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 28 = false ∨ valuation q 86 = false ∨ valuation q 92 = false := by
  rw [value28, value86, value87, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (49 : Vertex) (176 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 28 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value28, value87, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (49 : Vertex) (181 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 76 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value76, value86, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (176 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 76 = false ∨ valuation q 86 = false ∨ valuation q 92 = false := by
  rw [value76, value86, value87, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (176 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 76 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value76, value87, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (181 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value86, value87, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (176 : Vertex) (181 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 203 = true ∨ valuation q 76 = true ∨ valuation q 86 = true ∨ valuation q 90 = true ∨ valuation q 92 = true := by
  rw [value76, value86, value87, value90, value92, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(161 : Vertex), (176 : Vertex), (181 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (49 : Vertex) [(161 : Vertex), (176 : Vertex), (181 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 203 = true ∨ valuation q 28 = true ∨ valuation q 76 = true ∨ valuation q 86 = true ∨ valuation q 92 = true := by
  rw [value28, value76, value86, value87, value92, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(49 : Vertex), (161 : Vertex), (176 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (181 : Vertex) [(49 : Vertex), (161 : Vertex), (176 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 203 = true ∨ valuation q 28 = true ∨ valuation q 76 = true ∨ valuation q 86 = true ∨ valuation q 90 = true := by
  rw [value28, value76, value86, value87, value90, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(49 : Vertex), (161 : Vertex), (176 : Vertex), (181 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (185 : Vertex) [(49 : Vertex), (161 : Vertex), (176 : Vertex), (181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 29 = false ∨ valuation q 77 = false ∨ valuation q 86 = false := by
  rw [value29, value77, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (50 : Vertex) (162 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 29 = false ∨ valuation q 86 = false ∨ valuation q 93 = false := by
  rw [value29, value86, value88, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (50 : Vertex) (176 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 65 = false ∨ valuation q 86 = false ∨ valuation q 93 = false := by
  rw [value65, value86, value88, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (146 : Vertex) (176 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 67 = false ∨ valuation q 79 = false ∨ valuation q 86 = false := by
  rw [value67, value79, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (148 : Vertex) (164 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 79 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value79, value86, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (164 : Vertex) (176 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 205 = true ∨ valuation q 79 = true ∨ valuation q 86 = true ∨ valuation q 90 = true := by
  rw [value79, value86, value89, value90, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (180 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(164 : Vertex), (176 : Vertex), (181 : Vertex)] := by decide
  have hg := other_cover q (180 : Vertex) (148 : Vertex) [(164 : Vertex), (176 : Vertex), (181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 205 = true ∨ valuation q 67 = true ∨ valuation q 86 = true ∨ valuation q 90 = true := by
  rw [value67, value86, value89, value90, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (180 : Vertex) w → w ∈ region → w ≠ (164 : Vertex) → w ∈ [(148 : Vertex), (176 : Vertex), (181 : Vertex)] := by decide
  have hg := other_cover q (180 : Vertex) (164 : Vertex) [(148 : Vertex), (176 : Vertex), (181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 205 = true ∨ valuation q 67 = true ∨ valuation q 79 = true ∨ valuation q 90 = true := by
  rw [value67, value79, value89, value90, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (180 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(148 : Vertex), (164 : Vertex), (181 : Vertex)] := by decide
  have hg := other_cover q (180 : Vertex) (176 : Vertex) [(148 : Vertex), (164 : Vertex), (181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 205 = true ∨ valuation q 67 = true ∨ valuation q 79 = true ∨ valuation q 86 = true := by
  rw [value67, value79, value86, value89, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (180 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(148 : Vertex), (164 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (180 : Vertex) (181 : Vertex) [(148 : Vertex), (164 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block15 (q : Snake 81) (h : Conditions q) : B112E259.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112259
