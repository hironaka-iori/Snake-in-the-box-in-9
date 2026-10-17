import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 203 = true ∨ valuation q 88 = true := by
  rw [value87, value88, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (293 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(295 : Vertex)] := by decide
  have hg := other_cover q (293 : Vertex) (261 : Vertex) [(295 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 203 = true ∨ valuation q 80 = true := by
  rw [value80, value87, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (293 : Vertex) w → w ∈ region → w ≠ (295 : Vertex) → w ∈ [(261 : Vertex)] := by decide
  have hg := other_cover q (293 : Vertex) (295 : Vertex) [(261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 87 = false ∨ valuation q 105 = false := by
  rw [value87, value105, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (295 : Vertex) (293 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 204 = true ∨ valuation q 105 = true := by
  rw [value88, value105, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (293 : Vertex) → w ∈ [(423 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (293 : Vertex) [(423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 204 = true ∨ valuation q 87 = true := by
  rw [value87, value88, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(293 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (423 : Vertex) [(293 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 205 = true ∨ valuation q 90 = true := by
  rw [value89, value90, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (297 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(299 : Vertex)] := by decide
  have hg := other_cover q (297 : Vertex) (41 : Vertex) [(299 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 205 = true ∨ valuation q 24 = true := by
  rw [value24, value89, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (297 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(41 : Vertex)] := by decide
  have hg := other_cover q (297 : Vertex) (299 : Vertex) [(41 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 82 = false ∨ valuation q 89 = false ∨ valuation q 107 = false := by
  rw [value82, value89, value90, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (299 : Vertex) (267 : Vertex) (297 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 206 = true ∨ valuation q 89 = true ∨ valuation q 107 = true := by
  rw [value89, value90, value107, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(297 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (267 : Vertex) [(297 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 206 = true ∨ valuation q 82 = true ∨ valuation q 107 = true := by
  rw [value82, value90, value107, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(267 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (297 : Vertex) [(267 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 206 = true ∨ valuation q 82 = true ∨ valuation q 89 = true := by
  rw [value82, value89, value90, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(267 : Vertex), (297 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (427 : Vertex) [(267 : Vertex), (297 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 207 = true ∨ valuation q 92 = true := by
  rw [value91, value92, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (300 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(302 : Vertex)] := by decide
  have hg := other_cover q (300 : Vertex) (268 : Vertex) [(302 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 207 = true ∨ valuation q 83 = true := by
  rw [value83, value91, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (300 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(268 : Vertex)] := by decide
  have hg := other_cover q (300 : Vertex) (302 : Vertex) [(268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 208 = true ∨ valuation q 109 = true := by
  rw [value92, value109, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (300 : Vertex) → w ∈ [(430 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (300 : Vertex) [(430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 208 = true ∨ valuation q 91 = true := by
  rw [value91, value92, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(300 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (430 : Vertex) [(300 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 209 = true ∨ valuation q 110 = true := by
  rw [value93, value110, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (307 : Vertex) [(433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 209 = true ∨ valuation q 94 = true := by
  rw [value93, value94, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(307 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (433 : Vertex) [(307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 85 = false ∨ valuation q 93 = false ∨ valuation q 111 = false := by
  rw [value85, value93, value94, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (275 : Vertex) (305 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 210 = true ∨ valuation q 93 = true ∨ valuation q 111 = true := by
  rw [value93, value94, value111, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(305 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (275 : Vertex) [(305 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 210 = true ∨ valuation q 85 = true ∨ valuation q 111 = true := by
  rw [value85, value94, value111, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(275 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(275 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 210 = true ∨ valuation q 85 = true ∨ valuation q 93 = true := by
  rw [value85, value93, value94, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(275 : Vertex), (305 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (435 : Vertex) [(275 : Vertex), (305 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 96 = true := by
  rw [value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (308 : Vertex) w → w ∈ region → w ∈ [(310 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (308 : Vertex) [(310 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 95 = true := by
  rw [value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 212 = true ∨ valuation q 113 = true := by
  rw [value96, value113, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(438 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (308 : Vertex) [(438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 213 = true ∨ valuation q 99 = true := by
  rw [value97, value99, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(393 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (257 : Vertex) [(393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 213 = true ∨ valuation q 79 = true := by
  rw [value79, value97, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(257 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (393 : Vertex) [(257 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 214 = true ∨ valuation q 99 = true := by
  rw [value98, value99, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(393 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (264 : Vertex) [(393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 214 = true ∨ valuation q 81 = true := by
  rw [value81, value98, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(264 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (393 : Vertex) [(264 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 215 = true ∨ valuation q 98 = true := by
  rw [value98, value99, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (393 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(392 : Vertex)] := by decide
  have hg := other_cover q (393 : Vertex) (385 : Vertex) [(392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 215 = true ∨ valuation q 97 = true := by
  rw [value97, value99, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (393 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(385 : Vertex)] := by decide
  have hg := other_cover q (393 : Vertex) (392 : Vertex) [(385 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 45 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value45, value100, value101, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (399 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 84 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value84, value100, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (271 : Vertex) (398 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E257.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112257
