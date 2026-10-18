import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 198 = true ∨ valuation q 65 = true ∨ valuation q 70 = true ∨ valuation q 124 = true := by
  rw [value65, value70, value71, value124, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(243 : Vertex), (250 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (235 : Vertex) [(243 : Vertex), (250 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 198 = true ∨ valuation q 60 = true ∨ valuation q 65 = true ∨ valuation q 70 = true := by
  rw [value60, value65, value70, value71, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(235 : Vertex), (243 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (507 : Vertex) [(235 : Vertex), (243 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 33 = false ∨ valuation q 53 = false ∨ valuation q 61 = false := by
  rw [value33, value53, value61, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (253 : Vertex) (125 : Vertex) (221 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 33 = false ∨ valuation q 53 = false ∨ valuation q 67 = false := by
  rw [value33, value53, value67, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (253 : Vertex) (125 : Vertex) (221 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 33 = false ∨ valuation q 61 = false ∨ valuation q 67 = false := by
  rw [value33, value61, value67, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (253 : Vertex) (125 : Vertex) (237 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 53 = false ∨ valuation q 61 = false ∨ valuation q 67 = false := by
  rw [value53, value61, value67, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (253 : Vertex) (221 : Vertex) (237 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 53 = false ∨ valuation q 61 = false ∨ valuation q 126 = false := by
  rw [value53, value61, value72, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (253 : Vertex) (221 : Vertex) (237 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 199 = true ∨ valuation q 53 = true ∨ valuation q 61 = true ∨ valuation q 67 = true ∨ valuation q 126 = true := by
  rw [value53, value61, value67, value72, value126, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (253 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(221 : Vertex), (237 : Vertex), (245 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (253 : Vertex) (125 : Vertex) [(221 : Vertex), (237 : Vertex), (245 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 34 = false ∨ valuation q 62 = false ∨ valuation q 68 = false := by
  rw [value34, value62, value68, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (254 : Vertex) (126 : Vertex) (238 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 34 = false ∨ valuation q 62 = false ∨ valuation q 70 = false := by
  rw [value34, value62, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (254 : Vertex) (126 : Vertex) (238 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 34 = false ∨ valuation q 68 = false ∨ valuation q 70 = false := by
  rw [value34, value68, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (254 : Vertex) (126 : Vertex) (246 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 62 = false ∨ valuation q 68 = false ∨ valuation q 70 = false := by
  rw [value62, value68, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (254 : Vertex) (238 : Vertex) (246 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 200 = true ∨ valuation q 34 = true ∨ valuation q 68 = true ∨ valuation q 70 = true := by
  rw [value34, value68, value70, value73, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(126 : Vertex), (246 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (238 : Vertex) [(126 : Vertex), (246 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 200 = true ∨ valuation q 34 = true ∨ valuation q 62 = true ∨ valuation q 70 = true := by
  rw [value34, value62, value70, value73, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(126 : Vertex), (238 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (246 : Vertex) [(126 : Vertex), (238 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 74 = true := by
  rw [value74, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (281 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = true ∨ valuation q 87 = true := by
  rw [value74, value75, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ∈ [(285 : Vertex), (345 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (281 : Vertex) [(285 : Vertex), (345 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 75 = false ∨ valuation q 87 = false := by
  rw [value75, value87, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (281 : Vertex) (285 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 201 = true ∨ valuation q 87 = true := by
  rw [value74, value87, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (285 : Vertex) → w ∈ [(345 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (285 : Vertex) [(345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 201 = true ∨ valuation q 75 = true := by
  rw [value74, value75, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(285 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (345 : Vertex) [(285 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 90 = false := by
  rw [value74, value75, value76, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (285 : Vertex) (281 : Vertex) (317 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 202 = true ∨ valuation q 76 = true ∨ valuation q 90 = true := by
  rw [value75, value76, value90, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(317 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (281 : Vertex) [(317 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 202 = true ∨ valuation q 74 = true ∨ valuation q 90 = true := by
  rw [value74, value75, value90, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(281 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (317 : Vertex) [(281 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 202 = true ∨ valuation q 74 = true ∨ valuation q 76 = true := by
  rw [value74, value75, value76, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(281 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (349 : Vertex) [(281 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 76 = true := by
  rw [value76, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (317 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 99 = true := by
  rw [value75, value76, value77, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ∈ [(285 : Vertex), (319 : Vertex), (381 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (317 : Vertex) [(285 : Vertex), (319 : Vertex), (381 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 203 = true ∨ valuation q 77 = true ∨ valuation q 99 = true := by
  rw [value76, value77, value99, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (285 : Vertex) → w ∈ [(319 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (285 : Vertex) [(319 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 203 = true ∨ valuation q 75 = true ∨ valuation q 99 = true := by
  rw [value75, value76, value99, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (319 : Vertex) → w ∈ [(285 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (319 : Vertex) [(285 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 203 = true ∨ valuation q 75 = true ∨ valuation q 77 = true := by
  rw [value75, value76, value77, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (381 : Vertex) → w ∈ [(285 : Vertex), (319 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (381 : Vertex) [(285 : Vertex), (319 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 204 = true ∨ valuation q 101 = true := by
  rw [value77, value101, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (319 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(383 : Vertex)] := by decide
  have hg := other_cover q (319 : Vertex) (317 : Vertex) [(383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 78 = true := by
  rw [value78, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (329 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 6 = true ∨ valuation q 80 = true ∨ valuation q 87 = true := by
  rw [value6, value78, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ∈ [(73 : Vertex), (333 : Vertex), (345 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (329 : Vertex) [(73 : Vertex), (333 : Vertex), (345 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 6 = false ∨ valuation q 80 = false ∨ valuation q 87 = false := by
  rw [value6, value78, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (333 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E256.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112256
