import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 32 = false ∨ valuation q 48 = false := by
  rw [value16, value18, value32, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (276 : Vertex) (304 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 18 = false ∨ valuation q 48 = false := by
  rw [value18, value48, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (272 : Vertex) (276 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 19 = false ∨ valuation q 34 = false := by
  rw [value19, value34, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (275 : Vertex) (279 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 139 = true ∨ valuation q 34 = true := by
  rw [value17, value34, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(307 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (279 : Vertex) [(307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 139 = true ∨ valuation q 19 = true := by
  rw [value17, value19, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(279 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (307 : Vertex) [(279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 140 = true ∨ valuation q 35 = true ∨ valuation q 75 = true := by
  rw [value18, value35, value75, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(308 : Vertex), (404 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (272 : Vertex) [(308 : Vertex), (404 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 140 = true ∨ valuation q 16 = true ∨ valuation q 75 = true := by
  rw [value16, value18, value75, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(272 : Vertex), (404 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (308 : Vertex) [(272 : Vertex), (404 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 140 = true ∨ valuation q 16 = true ∨ valuation q 35 = true := by
  rw [value16, value18, value35, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(272 : Vertex), (308 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (404 : Vertex) [(272 : Vertex), (308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 10 = false ∨ valuation q 17 = false ∨ valuation q 23 = false := by
  rw [value10, value17, value19, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (275 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 10 = false ∨ valuation q 17 = false ∨ valuation q 76 = false := by
  rw [value10, value17, value19, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (275 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 10 = false ∨ valuation q 23 = false ∨ valuation q 76 = false := by
  rw [value10, value19, value23, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (287 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 141 = true ∨ valuation q 17 = true ∨ valuation q 23 = true ∨ valuation q 76 = true := by
  rw [value17, value19, value23, value76, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(275 : Vertex), (287 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (263 : Vertex) [(275 : Vertex), (287 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 141 = true ∨ valuation q 10 = true ∨ valuation q 23 = true ∨ valuation q 76 = true := by
  rw [value10, value19, value23, value76, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(263 : Vertex), (287 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (275 : Vertex) [(263 : Vertex), (287 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 141 = true ∨ valuation q 10 = true ∨ valuation q 17 = true ∨ valuation q 76 = true := by
  rw [value10, value17, value19, value76, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(263 : Vertex), (275 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (287 : Vertex) [(263 : Vertex), (275 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 141 = true ∨ valuation q 10 = true ∨ valuation q 17 = true ∨ valuation q 23 = true := by
  rw [value10, value17, value19, value23, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(263 : Vertex), (275 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (407 : Vertex) [(263 : Vertex), (275 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 12 = false ∨ valuation q 22 = false ∨ valuation q 51 = false := by
  rw [value12, value20, value22, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (285 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 12 = false ∨ valuation q 22 = false ∨ valuation q 77 = false := by
  rw [value12, value20, value22, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (285 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 12 = false ∨ valuation q 51 = false ∨ valuation q 77 = false := by
  rw [value12, value20, value51, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (345 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 51 = false ∨ valuation q 77 = false := by
  rw [value20, value22, value51, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (285 : Vertex) (345 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 22 = false ∨ valuation q 51 = false := by
  rw [value22, value51, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (281 : Vertex) (285 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 38 = false ∨ valuation q 78 = false := by
  rw [value38, value78, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (282 : Vertex) (314 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 143 = true ∨ valuation q 78 = true := by
  rw [value21, value78, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(410 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (314 : Vertex) [(410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 143 = true ∨ valuation q 38 = true := by
  rw [value21, value38, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(314 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (410 : Vertex) [(314 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 23 = false ∨ valuation q 80 = false := by
  rw [value20, value22, value23, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (285 : Vertex) (281 : Vertex) (287 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 144 = true ∨ valuation q 23 = true ∨ valuation q 39 = true ∨ valuation q 80 = true := by
  rw [value22, value23, value39, value80, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(287 : Vertex), (317 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (281 : Vertex) [(287 : Vertex), (317 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 144 = true ∨ valuation q 20 = true ∨ valuation q 39 = true ∨ valuation q 80 = true := by
  rw [value20, value22, value39, value80, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(281 : Vertex), (317 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (287 : Vertex) [(281 : Vertex), (317 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 144 = true ∨ valuation q 20 = true ∨ valuation q 23 = true ∨ valuation q 80 = true := by
  rw [value20, value22, value23, value80, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(281 : Vertex), (287 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (317 : Vertex) [(281 : Vertex), (287 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 144 = true ∨ valuation q 20 = true ∨ valuation q 23 = true ∨ valuation q 39 = true := by
  rw [value20, value22, value23, value39, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(281 : Vertex), (287 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (413 : Vertex) [(281 : Vertex), (287 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 23 = true := by
  rw [value23, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (287 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 22 = false := by
  rw [value15, value19, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (279 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 41 = false := by
  rw [value15, value19, value23, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (279 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 81 = false := by
  rw [value15, value19, value23, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (279 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E254.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112254
