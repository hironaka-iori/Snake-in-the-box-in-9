import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 54 = false ∨ valuation q 64 = false ∨ valuation q 96 = false := by
  rw [value43, value54, value64, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (155 : Vertex) (203 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 65 = true ∨ valuation q 97 = true := by
  rw [value38, value40, value44, value65, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ∈ [(132 : Vertex), (136 : Vertex), (204 : Vertex), (396 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (140 : Vertex) [(132 : Vertex), (136 : Vertex), (204 : Vertex), (396 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 65 = false := by
  rw [value38, value40, value44, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (132 : Vertex) (136 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 168 = true ∨ valuation q 40 = true ∨ valuation q 65 = true ∨ valuation q 97 = true := by
  rw [value40, value44, value65, value97, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(136 : Vertex), (204 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (132 : Vertex) [(136 : Vertex), (204 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 168 = true ∨ valuation q 38 = true ∨ valuation q 65 = true ∨ valuation q 97 = true := by
  rw [value38, value44, value65, value97, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(132 : Vertex), (204 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (136 : Vertex) [(132 : Vertex), (204 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 168 = true ∨ valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 97 = true := by
  rw [value38, value40, value44, value97, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(132 : Vertex), (136 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (204 : Vertex) [(132 : Vertex), (136 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 168 = true ∨ valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 65 = true := by
  rw [value38, value40, value44, value65, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(132 : Vertex), (136 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (396 : Vertex) [(132 : Vertex), (136 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 45 = true := by
  rw [value45, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (143 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 43 = true ∨ valuation q 55 = true ∨ valuation q 68 = true := by
  rw [value43, value45, value55, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ∈ [(139 : Vertex), (159 : Vertex), (207 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (143 : Vertex) [(139 : Vertex), (159 : Vertex), (207 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 43 = false ∨ valuation q 55 = false ∨ valuation q 68 = false := by
  rw [value43, value45, value55, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (143 : Vertex) (139 : Vertex) (159 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 55 = false ∨ valuation q 68 = false := by
  rw [value55, value68, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (143 : Vertex) (159 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 169 = true ∨ valuation q 55 = true ∨ valuation q 68 = true := by
  rw [value45, value55, value68, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(159 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (139 : Vertex) [(159 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 169 = true ∨ valuation q 43 = true ∨ valuation q 68 = true := by
  rw [value43, value45, value68, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(139 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (159 : Vertex) [(139 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 169 = true ∨ valuation q 43 = true ∨ valuation q 55 = true := by
  rw [value43, value45, value55, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(139 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (207 : Vertex) [(139 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 46 = true := by
  rw [value46, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (145 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 36 = false ∨ valuation q 48 = false ∨ valuation q 70 = false := by
  rw [value36, value46, value48, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (129 : Vertex) (149 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 36 = false ∨ valuation q 48 = false ∨ valuation q 100 = false := by
  rw [value36, value46, value48, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (129 : Vertex) (149 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 36 = false ∨ valuation q 70 = false ∨ valuation q 100 = false := by
  rw [value36, value46, value70, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (129 : Vertex) (209 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 70 = false := by
  rw [value46, value48, value52, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (149 : Vertex) (153 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 100 = false := by
  rw [value46, value48, value52, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (149 : Vertex) (153 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 70 = false ∨ valuation q 100 = false := by
  rw [value46, value48, value70, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (149 : Vertex) (209 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 52 = false ∨ valuation q 70 = false ∨ valuation q 100 = false := by
  rw [value46, value52, value70, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (153 : Vertex) (209 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 170 = true ∨ valuation q 36 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 100 = true := by
  rw [value36, value46, value48, value52, value100, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(129 : Vertex), (149 : Vertex), (153 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (209 : Vertex) [(129 : Vertex), (149 : Vertex), (153 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 170 = true ∨ valuation q 36 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 70 = true := by
  rw [value36, value46, value48, value52, value70, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(129 : Vertex), (149 : Vertex), (153 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (401 : Vertex) [(129 : Vertex), (149 : Vertex), (153 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 47 = true := by
  rw [value47, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (148 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 38 = true ∨ valuation q 48 = true ∨ valuation q 49 = true := by
  rw [value38, value47, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ∈ [(132 : Vertex), (149 : Vertex), (150 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (148 : Vertex) [(132 : Vertex), (149 : Vertex), (150 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 171 = true ∨ valuation q 48 = true ∨ valuation q 49 = true := by
  rw [value47, value48, value49, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(149 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (132 : Vertex) [(149 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 171 = true ∨ valuation q 38 = true ∨ valuation q 49 = true := by
  rw [value38, value47, value49, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(132 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (149 : Vertex) [(132 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 171 = true ∨ valuation q 38 = true ∨ valuation q 48 = true := by
  rw [value38, value47, value48, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(132 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (150 : Vertex) [(132 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value46, value47, value48, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (145 : Vertex) (148 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 172 = true ∨ valuation q 47 = true ∨ valuation q 50 = true := by
  rw [value47, value48, value50, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(148 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (145 : Vertex) [(148 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 172 = true ∨ valuation q 46 = true ∨ valuation q 50 = true := by
  rw [value46, value48, value50, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(145 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (148 : Vertex) [(145 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block9 (q : Snake 81) (h : Conditions q) : B112E089.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112089
