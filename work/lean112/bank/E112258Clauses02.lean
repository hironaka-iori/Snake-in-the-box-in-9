import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 34 = false ∨ valuation q 74 = false := by
  rw [value14, value15, value34, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (272 : Vertex) (305 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 34 = false := by
  rw [value15, value16, value19, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (275 : Vertex) (281 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 46 = false := by
  rw [value15, value16, value19, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (275 : Vertex) (281 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 74 = false := by
  rw [value15, value16, value19, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (275 : Vertex) (281 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 34 = false ∨ valuation q 74 = false := by
  rw [value15, value19, value34, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (281 : Vertex) (305 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 16 = true := by
  rw [value16, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (275 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 35 = false := by
  rw [value15, value16, value18, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (273 : Vertex) (279 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 18 = false ∨ valuation q 35 = false := by
  rw [value18, value35, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (275 : Vertex) (279 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 138 = true ∨ valuation q 18 = true ∨ valuation q 35 = true := by
  rw [value16, value18, value35, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (273 : Vertex) → w ∈ [(279 : Vertex), (307 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (273 : Vertex) [(279 : Vertex), (307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 138 = true ∨ valuation q 15 = true ∨ valuation q 35 = true := by
  rw [value15, value16, value35, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(273 : Vertex), (307 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (279 : Vertex) [(273 : Vertex), (307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 138 = true ∨ valuation q 15 = true ∨ valuation q 18 = true := by
  rw [value15, value16, value18, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(273 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (307 : Vertex) [(273 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 14 = false ∨ valuation q 36 = false ∨ valuation q 75 = false := by
  rw [value14, value17, value36, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (272 : Vertex) (308 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 139 = true ∨ valuation q 36 = true ∨ valuation q 75 = true := by
  rw [value17, value36, value75, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(308 : Vertex), (404 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (272 : Vertex) [(308 : Vertex), (404 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 139 = true ∨ valuation q 14 = true ∨ valuation q 75 = true := by
  rw [value14, value17, value75, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(272 : Vertex), (404 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (308 : Vertex) [(272 : Vertex), (404 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 139 = true ∨ valuation q 14 = true ∨ valuation q 36 = true := by
  rw [value14, value17, value36, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(272 : Vertex), (308 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (404 : Vertex) [(272 : Vertex), (308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 9 = false ∨ valuation q 16 = false ∨ valuation q 23 = false := by
  rw [value9, value16, value18, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (275 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 9 = false ∨ valuation q 16 = false ∨ valuation q 76 = false := by
  rw [value9, value16, value18, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (275 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 140 = true ∨ valuation q 16 = true ∨ valuation q 23 = true ∨ valuation q 76 = true := by
  rw [value16, value18, value23, value76, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(275 : Vertex), (287 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (263 : Vertex) [(275 : Vertex), (287 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 140 = true ∨ valuation q 9 = true ∨ valuation q 23 = true ∨ valuation q 76 = true := by
  rw [value9, value18, value23, value76, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(263 : Vertex), (287 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (275 : Vertex) [(263 : Vertex), (287 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 140 = true ∨ valuation q 9 = true ∨ valuation q 16 = true ∨ valuation q 23 = true := by
  rw [value9, value16, value18, value23, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(263 : Vertex), (275 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (407 : Vertex) [(263 : Vertex), (275 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 15 = false ∨ valuation q 21 = false := by
  rw [value15, value21, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (281 : Vertex) (273 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 141 = true ∨ valuation q 21 = true ∨ valuation q 77 = true := by
  rw [value19, value21, value77, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (273 : Vertex) → w ∈ [(285 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (273 : Vertex) [(285 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 141 = true ∨ valuation q 15 = true ∨ valuation q 77 = true := by
  rw [value15, value19, value77, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (285 : Vertex) → w ∈ [(273 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (285 : Vertex) [(273 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 141 = true ∨ valuation q 15 = true ∨ valuation q 21 = true := by
  rw [value15, value19, value21, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(273 : Vertex), (285 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (409 : Vertex) [(273 : Vertex), (285 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 39 = false ∨ valuation q 78 = false := by
  rw [value20, value22, value39, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (286 : Vertex) (314 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 22 = false ∨ valuation q 39 = false := by
  rw [value22, value39, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (282 : Vertex) (286 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 142 = true ∨ valuation q 39 = true ∨ valuation q 78 = true := by
  rw [value20, value39, value78, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (286 : Vertex) → w ∈ [(314 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (286 : Vertex) [(314 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 142 = true ∨ valuation q 22 = true ∨ valuation q 78 = true := by
  rw [value20, value22, value78, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(286 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (314 : Vertex) [(286 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 142 = true ∨ valuation q 22 = true ∨ valuation q 39 = true := by
  rw [value20, value22, value39, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(286 : Vertex), (314 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (410 : Vertex) [(286 : Vertex), (314 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 143 = true ∨ valuation q 23 = true ∨ valuation q 40 = true := by
  rw [value21, value23, value40, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(287 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (281 : Vertex) [(287 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 143 = true ∨ valuation q 19 = true ∨ valuation q 40 = true := by
  rw [value19, value21, value40, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(281 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (287 : Vertex) [(281 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 143 = true ∨ valuation q 19 = true ∨ valuation q 23 = true := by
  rw [value19, value21, value23, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(281 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (317 : Vertex) [(281 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E258.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112258
