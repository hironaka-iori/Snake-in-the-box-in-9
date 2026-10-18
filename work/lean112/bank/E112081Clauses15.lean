import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 20 = false ∨ valuation q 52 = false ∨ valuation q 89 = false := by
  rw [value20, value52, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (135 : Vertex) (263 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 20 = false ∨ valuation q 52 = false ∨ valuation q 95 = false := by
  rw [value20, value52, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (135 : Vertex) (263 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 20 = false ∨ valuation q 89 = false ∨ valuation q 95 = false := by
  rw [value20, value89, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (135 : Vertex) (390 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 52 = false ∨ valuation q 89 = false ∨ valuation q 95 = false := by
  rw [value52, value89, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (263 : Vertex) (390 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 207 = true ∨ valuation q 52 = true ∨ valuation q 89 = true ∨ valuation q 95 = true := by
  rw [value52, value89, value90, value95, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(263 : Vertex), (390 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (135 : Vertex) [(263 : Vertex), (390 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 21 = false ∨ valuation q 87 = false ∨ valuation q 92 = false := by
  rw [value21, value87, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (136 : Vertex) (384 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 53 = false ∨ valuation q 87 = false ∨ valuation q 92 = false := by
  rw [value53, value87, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (264 : Vertex) (384 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 22 = false ∨ valuation q 88 = false ∨ valuation q 94 = false := by
  rw [value22, value88, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (385 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value88, value91, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (385 : Vertex) (392 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 209 = true ∨ valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 93 = true ∨ valuation q 94 = true := by
  rw [value88, value91, value92, value93, value94, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (393 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(385 : Vertex), (392 : Vertex), (395 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (393 : Vertex) (137 : Vertex) [(385 : Vertex), (392 : Vertex), (395 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 55 = false ∨ valuation q 92 = false ∨ valuation q 95 = false := by
  rw [value55, value92, value93, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (267 : Vertex) (393 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 210 = true ∨ valuation q 55 = true ∨ valuation q 92 = true := by
  rw [value55, value92, value93, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(267 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (399 : Vertex) [(267 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 102 = false := by
  rw [value92, value94, value95, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (393 : Vertex) (399 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 211 = true ∨ valuation q 92 = true ∨ valuation q 102 = true := by
  rw [value92, value94, value102, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(393 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (399 : Vertex) [(393 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 211 = true ∨ valuation q 92 = true ∨ valuation q 95 = true := by
  rw [value92, value94, value95, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(393 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (413 : Vertex) [(393 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 58 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value58, value90, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (271 : Vertex) (391 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 212 = true ∨ valuation q 90 = true ∨ valuation q 93 = true ∨ valuation q 94 = true := by
  rw [value90, value93, value94, value95, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(391 : Vertex), (395 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (271 : Vertex) [(391 : Vertex), (395 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 212 = true ∨ valuation q 58 = true ∨ valuation q 93 = true ∨ valuation q 94 = true := by
  rw [value58, value93, value94, value95, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(271 : Vertex), (395 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (391 : Vertex) [(271 : Vertex), (395 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 212 = true ∨ valuation q 58 = true ∨ valuation q 90 = true ∨ valuation q 94 = true := by
  rw [value58, value90, value94, value95, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (395 : Vertex) → w ∈ [(271 : Vertex), (391 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (395 : Vertex) [(271 : Vertex), (391 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 212 = true ∨ valuation q 58 = true ∨ valuation q 90 = true ∨ valuation q 93 = true := by
  rw [value58, value90, value93, value95, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(271 : Vertex), (391 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (397 : Vertex) [(271 : Vertex), (391 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 213 = true ∨ valuation q 88 = true ∨ valuation q 98 = true := by
  rw [value88, value96, value98, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (273 : Vertex) → w ∈ [(385 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (273 : Vertex) [(385 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 213 = true ∨ valuation q 59 = true ∨ valuation q 98 = true := by
  rw [value59, value96, value98, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(273 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (385 : Vertex) [(273 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 213 = true ∨ valuation q 59 = true ∨ valuation q 88 = true := by
  rw [value59, value88, value96, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(273 : Vertex), (385 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (403 : Vertex) [(273 : Vertex), (385 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 214 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value97, value99, value100, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(406 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (403 : Vertex) [(406 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 214 = true ∨ valuation q 98 = true ∨ valuation q 100 = true := by
  rw [value97, value98, value100, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(403 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (406 : Vertex) [(403 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 214 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value97, value98, value99, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(403 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (410 : Vertex) [(403 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 60 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value60, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (275 : Vertex) (401 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value96, value97, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (403 : Vertex) (401 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 215 = true ∨ valuation q 60 = true ∨ valuation q 96 = true := by
  rw [value60, value96, value98, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(275 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (402 : Vertex) [(275 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 89 = false ∨ valuation q 97 = false ∨ valuation q 103 = false := by
  rw [value89, value97, value99, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (390 : Vertex) (402 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 30 = false ∨ valuation q 66 = false ∨ valuation q 97 = false := by
  rw [value30, value66, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (154 : Vertex) (282 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 30 = false ∨ valuation q 66 = false ∨ valuation q 103 = false := by
  rw [value30, value66, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (154 : Vertex) (282 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E081.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112081
