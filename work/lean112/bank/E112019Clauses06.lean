import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 41 = false ∨ valuation q 44 = false ∨ valuation q 54 = false := by
  rw [value41, value44, value45, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 41 = false ∨ valuation q 46 = false ∨ valuation q 54 = false := by
  rw [value41, value45, value46, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (203 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 54 = false := by
  rw [value44, value45, value46, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (200 : Vertex) (203 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 166 = true ∨ valuation q 41 = true ∨ valuation q 46 = true ∨ valuation q 54 = true := by
  rw [value41, value45, value46, value54, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(193 : Vertex), (203 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (200 : Vertex) [(193 : Vertex), (203 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 166 = true ∨ valuation q 41 = true ∨ valuation q 44 = true ∨ valuation q 54 = true := by
  rw [value41, value44, value45, value54, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(193 : Vertex), (200 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (203 : Vertex) [(193 : Vertex), (200 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 166 = true ∨ valuation q 41 = true ∨ valuation q 44 = true ∨ valuation q 46 = true := by
  rw [value41, value44, value45, value46, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(193 : Vertex), (200 : Vertex), (203 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (217 : Vertex) [(193 : Vertex), (200 : Vertex), (203 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 12 = true ∨ valuation q 29 = true ∨ valuation q 45 = true ∨ valuation q 56 = true ∨ valuation q 106 = true := by
  rw [value12, value29, value45, value46, value56, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ∈ [(75 : Vertex), (139 : Vertex), (201 : Vertex), (219 : Vertex), (459 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (203 : Vertex) [(75 : Vertex), (139 : Vertex), (201 : Vertex), (219 : Vertex), (459 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 12 = false ∨ valuation q 29 = false ∨ valuation q 45 = false := by
  rw [value12, value29, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (75 : Vertex) (139 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 12 = false ∨ valuation q 29 = false ∨ valuation q 56 = false := by
  rw [value12, value29, value46, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (75 : Vertex) (139 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 12 = false ∨ valuation q 56 = false ∨ valuation q 106 = false := by
  rw [value12, value46, value56, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (75 : Vertex) (219 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 29 = false ∨ valuation q 56 = false ∨ valuation q 106 = false := by
  rw [value29, value46, value56, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (139 : Vertex) (219 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 45 = false ∨ valuation q 56 = false ∨ valuation q 106 = false := by
  rw [value45, value46, value56, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (201 : Vertex) (219 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 12 = false ∨ valuation q 56 = false := by
  rw [value12, value56, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (203 : Vertex) (75 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 56 = false ∨ valuation q 106 = false := by
  rw [value56, value106, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (203 : Vertex) (219 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 167 = true ∨ valuation q 29 = true ∨ valuation q 45 = true ∨ valuation q 56 = true ∨ valuation q 106 = true := by
  rw [value29, value45, value46, value56, value106, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(139 : Vertex), (201 : Vertex), (219 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (75 : Vertex) [(139 : Vertex), (201 : Vertex), (219 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 167 = true ∨ valuation q 12 = true ∨ valuation q 45 = true ∨ valuation q 56 = true ∨ valuation q 106 = true := by
  rw [value12, value45, value46, value56, value106, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(75 : Vertex), (201 : Vertex), (219 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (139 : Vertex) [(75 : Vertex), (201 : Vertex), (219 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 167 = true ∨ valuation q 12 = true ∨ valuation q 29 = true ∨ valuation q 56 = true ∨ valuation q 106 = true := by
  rw [value12, value29, value46, value56, value106, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(75 : Vertex), (139 : Vertex), (219 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (201 : Vertex) [(75 : Vertex), (139 : Vertex), (219 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 167 = true ∨ valuation q 12 = true ∨ valuation q 29 = true ∨ valuation q 45 = true ∨ valuation q 106 = true := by
  rw [value12, value29, value45, value46, value106, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(75 : Vertex), (139 : Vertex), (201 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (219 : Vertex) [(75 : Vertex), (139 : Vertex), (201 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 167 = true ∨ valuation q 12 = true ∨ valuation q 29 = true ∨ valuation q 45 = true ∨ valuation q 56 = true := by
  rw [value12, value29, value45, value46, value56, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(75 : Vertex), (139 : Vertex), (201 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (459 : Vertex) [(75 : Vertex), (139 : Vertex), (201 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 44 = false ∨ valuation q 48 = false ∨ valuation q 107 = false := by
  rw [value44, value47, value48, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (200 : Vertex) (206 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 168 = true ∨ valuation q 48 = true ∨ valuation q 107 = true := by
  rw [value47, value48, value107, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(206 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (200 : Vertex) [(206 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 168 = true ∨ valuation q 44 = true ∨ valuation q 107 = true := by
  rw [value44, value47, value107, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(200 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (206 : Vertex) [(200 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 168 = true ∨ valuation q 44 = true ∨ valuation q 48 = true := by
  rw [value44, value47, value48, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (460 : Vertex) → w ∈ [(200 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (460 : Vertex) [(200 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 48 = true := by
  rw [value48, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (206 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 42 = true ∨ valuation q 47 = true ∨ valuation q 109 = true := by
  rw [value42, value47, value48, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ∈ [(198 : Vertex), (204 : Vertex), (462 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (206 : Vertex) [(198 : Vertex), (204 : Vertex), (462 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 42 = false ∨ valuation q 47 = false ∨ valuation q 109 = false := by
  rw [value42, value47, value48, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (204 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 47 = false ∨ valuation q 109 = false := by
  rw [value47, value109, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (206 : Vertex) (204 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 169 = true ∨ valuation q 47 = true ∨ valuation q 109 = true := by
  rw [value47, value48, value109, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(204 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (198 : Vertex) [(204 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 169 = true ∨ valuation q 42 = true ∨ valuation q 109 = true := by
  rw [value42, value48, value109, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(198 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (204 : Vertex) [(198 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 169 = true ∨ valuation q 42 = true ∨ valuation q 47 = true := by
  rw [value42, value47, value48, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(198 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (462 : Vertex) [(198 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 113 = false := by
  rw [value49, value52, value55, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (214 : Vertex) (218 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 170 = true ∨ valuation q 55 = true ∨ valuation q 113 = true := by
  rw [value49, value55, value113, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(218 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (214 : Vertex) [(218 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E019.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112019
