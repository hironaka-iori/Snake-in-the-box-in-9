import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value38, value40, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (133 : Vertex) (134 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 52 = false := by
  rw [value38, value40, value42, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (133 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 38 = false ∨ valuation q 41 = false ∨ valuation q 52 = false := by
  rw [value38, value41, value42, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (134 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 52 = false := by
  rw [value40, value41, value42, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (133 : Vertex) (134 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 170 = true ∨ valuation q 40 = true ∨ valuation q 41 = true ∨ valuation q 52 = true := by
  rw [value40, value41, value42, value52, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (135 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(133 : Vertex), (134 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (135 : Vertex) (131 : Vertex) [(133 : Vertex), (134 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 170 = true ∨ valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 41 = true := by
  rw [value38, value40, value41, value42, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (135 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(131 : Vertex), (133 : Vertex), (134 : Vertex)] := by decide
  have hg := other_cover q (135 : Vertex) (151 : Vertex) [(131 : Vertex), (133 : Vertex), (134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 5 = false ∨ valuation q 44 = false ∨ valuation q 45 = false := by
  rw [value5, value43, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (8 : Vertex) (137 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 5 = false ∨ valuation q 44 = false ∨ valuation q 53 = false := by
  rw [value5, value43, value44, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (8 : Vertex) (137 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 5 = false ∨ valuation q 45 = false ∨ valuation q 53 = false := by
  rw [value5, value43, value45, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (8 : Vertex) (138 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 53 = false := by
  rw [value43, value44, value45, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (138 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 43 = true ∨ valuation q 46 = true ∨ valuation q 47 = true := by
  rw [value43, value44, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ∈ [(136 : Vertex), (139 : Vertex), (141 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (137 : Vertex) [(136 : Vertex), (139 : Vertex), (141 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 172 = true ∨ valuation q 46 = true ∨ valuation q 47 = true := by
  rw [value44, value46, value47, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(139 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (136 : Vertex) [(139 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 172 = true ∨ valuation q 43 = true ∨ valuation q 47 = true := by
  rw [value43, value44, value47, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(136 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (139 : Vertex) [(136 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 172 = true ∨ valuation q 43 = true ∨ valuation q 46 = true := by
  rw [value43, value44, value46, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(136 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (141 : Vertex) [(136 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 6 = false ∨ valuation q 46 = false ∨ valuation q 54 = false := by
  rw [value6, value45, value46, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (10 : Vertex) (139 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 43 = false ∨ valuation q 46 = false ∨ valuation q 60 = false := by
  rw [value43, value45, value46, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (136 : Vertex) (139 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 54 = false ∨ valuation q 60 = false := by
  rw [value45, value46, value54, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (139 : Vertex) (154 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 54 = false ∨ valuation q 113 = false := by
  rw [value45, value46, value54, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (139 : Vertex) (154 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 60 = false ∨ valuation q 113 = false := by
  rw [value45, value46, value60, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (139 : Vertex) (202 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 38 = false ∨ valuation q 44 = false ∨ valuation q 45 = false := by
  rw [value38, value44, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 174 = true ∨ valuation q 38 = true ∨ valuation q 45 = true := by
  rw [value38, value45, value46, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(131 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (137 : Vertex) [(131 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 175 = true ∨ valuation q 40 = true ∨ valuation q 115 = true := by
  rw [value40, value47, value115, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(133 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (137 : Vertex) [(133 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 175 = true ∨ valuation q 40 = true ∨ valuation q 44 = true := by
  rw [value40, value44, value47, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(133 : Vertex), (137 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (397 : Vertex) [(133 : Vertex), (137 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 53 = false ∨ valuation q 64 = false := by
  rw [value48, value49, value53, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (148 : Vertex) (152 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 53 = false ∨ valuation q 118 = false := by
  rw [value48, value49, value53, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (148 : Vertex) (152 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 64 = false ∨ valuation q 118 = false := by
  rw [value48, value49, value64, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (148 : Vertex) (208 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 64 = false ∨ valuation q 118 = false := by
  rw [value48, value53, value64, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (152 : Vertex) (208 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 39 = true ∨ valuation q 48 = true ∨ valuation q 50 = true ∨ valuation q 51 = true := by
  rw [value39, value48, value49, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ∈ [(132 : Vertex), (144 : Vertex), (149 : Vertex), (150 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (148 : Vertex) [(132 : Vertex), (144 : Vertex), (149 : Vertex), (150 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 39 = false ∨ valuation q 48 = false ∨ valuation q 50 = false := by
  rw [value39, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (132 : Vertex) (144 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 177 = true ∨ valuation q 48 = true ∨ valuation q 50 = true ∨ valuation q 51 = true := by
  rw [value48, value49, value50, value51, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(144 : Vertex), (149 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (132 : Vertex) [(144 : Vertex), (149 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 177 = true ∨ valuation q 39 = true ∨ valuation q 50 = true ∨ valuation q 51 = true := by
  rw [value39, value49, value50, value51, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(132 : Vertex), (149 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (144 : Vertex) [(132 : Vertex), (149 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 177 = true ∨ valuation q 39 = true ∨ valuation q 48 = true ∨ valuation q 50 = true := by
  rw [value39, value48, value49, value50, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(132 : Vertex), (144 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (150 : Vertex) [(132 : Vertex), (144 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block9 (q : Snake 81) (h : Conditions q) : B112E055.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112055
