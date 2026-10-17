import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 131 = true ∨ valuation q 13 = true ∨ valuation q 18 = true ∨ valuation q 28 = true ∨ valuation q 69 = true := by
  rw [value9, value13, value18, value28, value69, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(271 : Vertex), (279 : Vertex), (295 : Vertex), (391 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (261 : Vertex) [(271 : Vertex), (279 : Vertex), (295 : Vertex), (391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 29 = false ∨ valuation q 44 = false := by
  rw [value10, value12, value29, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (268 : Vertex) (296 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 12 = false ∨ valuation q 44 = false := by
  rw [value12, value44, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (264 : Vertex) (268 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 132 = true ∨ valuation q 29 = true ∨ valuation q 44 = true := by
  rw [value10, value29, value44, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(296 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (268 : Vertex) [(296 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 13 = false ∨ valuation q 31 = false := by
  rw [value13, value31, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (267 : Vertex) (271 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 133 = true ∨ valuation q 31 = true := by
  rw [value11, value31, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(299 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (271 : Vertex) [(299 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 133 = true ∨ valuation q 13 = true := by
  rw [value11, value13, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(271 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (299 : Vertex) [(271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 134 = true ∨ valuation q 32 = true ∨ valuation q 71 = true := by
  rw [value12, value32, value71, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(300 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (264 : Vertex) [(300 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 134 = true ∨ valuation q 10 = true ∨ valuation q 71 = true := by
  rw [value10, value12, value71, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (300 : Vertex) → w ∈ [(264 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (300 : Vertex) [(264 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 134 = true ∨ valuation q 10 = true ∨ valuation q 32 = true := by
  rw [value10, value12, value32, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(264 : Vertex), (300 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (396 : Vertex) [(264 : Vertex), (300 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 9 = false ∨ valuation q 11 = false ∨ valuation q 23 = false := by
  rw [value9, value11, value13, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 9 = false ∨ valuation q 11 = false ∨ valuation q 72 = false := by
  rw [value9, value11, value13, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 9 = false ∨ valuation q 23 = false ∨ valuation q 72 = false := by
  rw [value9, value13, value23, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (287 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 11 = false ∨ valuation q 23 = false ∨ valuation q 72 = false := by
  rw [value11, value13, value23, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (287 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 135 = true ∨ valuation q 11 = true ∨ valuation q 23 = true ∨ valuation q 72 = true := by
  rw [value11, value13, value23, value72, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(267 : Vertex), (287 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (263 : Vertex) [(267 : Vertex), (287 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 135 = true ∨ valuation q 9 = true ∨ valuation q 23 = true ∨ valuation q 72 = true := by
  rw [value9, value13, value23, value72, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(263 : Vertex), (287 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (267 : Vertex) [(263 : Vertex), (287 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 135 = true ∨ valuation q 9 = true ∨ valuation q 11 = true ∨ valuation q 72 = true := by
  rw [value9, value11, value13, value72, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(263 : Vertex), (267 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (287 : Vertex) [(263 : Vertex), (267 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 135 = true ∨ valuation q 9 = true ∨ valuation q 11 = true ∨ valuation q 23 = true := by
  rw [value9, value11, value13, value23, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(263 : Vertex), (267 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (399 : Vertex) [(263 : Vertex), (267 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 73 = false := by
  rw [value14, value15, value17, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (273 : Vertex) (276 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 136 = true ∨ valuation q 15 = true ∨ valuation q 73 = true := by
  rw [value14, value15, value73, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(273 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (276 : Vertex) [(273 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 136 = true ∨ valuation q 15 = true ∨ valuation q 17 = true := by
  rw [value14, value15, value17, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(273 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (400 : Vertex) [(273 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value6, value14, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (257 : Vertex) (272 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 19 = false := by
  rw [value6, value14, value15, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (257 : Vertex) (272 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 34 = false := by
  rw [value6, value14, value15, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (257 : Vertex) (272 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 46 = false := by
  rw [value6, value14, value15, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (257 : Vertex) (272 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 16 = false ∨ valuation q 19 = false := by
  rw [value6, value15, value16, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (257 : Vertex) (275 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 34 = false := by
  rw [value6, value15, value19, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (257 : Vertex) (281 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 74 = false := by
  rw [value6, value15, value19, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (257 : Vertex) (281 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 19 = false := by
  rw [value14, value15, value16, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (272 : Vertex) (275 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 74 = false := by
  rw [value14, value15, value16, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (272 : Vertex) (275 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 34 = false := by
  rw [value14, value15, value19, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (272 : Vertex) (281 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 74 = false := by
  rw [value14, value15, value19, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (272 : Vertex) (281 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E258.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112258
