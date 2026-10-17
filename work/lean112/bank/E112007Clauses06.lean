import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 170 = true ∨ valuation q 50 = true ∨ valuation q 70 = true := by
  rw [value50, value52, value70, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(258 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (394 : Vertex) [(258 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value53, value54, value55, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (273 : Vertex) (274 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 59 = false := by
  rw [value53, value54, value55, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (273 : Vertex) (274 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 57 = false ∨ valuation q 59 = false := by
  rw [value53, value54, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (273 : Vertex) (276 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 59 = false := by
  rw [value53, value55, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (274 : Vertex) (276 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 171 = true ∨ valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 59 = true := by
  rw [value53, value54, value55, value59, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(273 : Vertex), (274 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (276 : Vertex) [(273 : Vertex), (274 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 171 = true ∨ valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 57 = true := by
  rw [value53, value54, value55, value57, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(273 : Vertex), (274 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (280 : Vertex) [(273 : Vertex), (274 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 54 = true := by
  rw [value54, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (273 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = true ∨ valuation q 56 = true ∨ valuation q 91 = true := by
  rw [value53, value54, value56, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (273 : Vertex) w → w ∈ region → w ∈ [(272 : Vertex), (275 : Vertex), (401 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (273 : Vertex) [(272 : Vertex), (275 : Vertex), (401 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 53 = false ∨ valuation q 91 = false := by
  rw [value53, value91, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (273 : Vertex) (272 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 56 = false ∨ valuation q 91 = false := by
  rw [value56, value91, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (273 : Vertex) (275 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 172 = true ∨ valuation q 56 = true ∨ valuation q 91 = true := by
  rw [value54, value56, value91, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (273 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(275 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (273 : Vertex) (272 : Vertex) [(275 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 172 = true ∨ valuation q 53 = true ∨ valuation q 91 = true := by
  rw [value53, value54, value91, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (273 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(272 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (273 : Vertex) (275 : Vertex) [(272 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 172 = true ∨ valuation q 53 = true ∨ valuation q 56 = true := by
  rw [value53, value54, value56, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (273 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(272 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (273 : Vertex) (401 : Vertex) [(272 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value51, value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (259 : Vertex) (273 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 92 = false := by
  rw [value51, value54, value56, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (259 : Vertex) (273 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 92 = false := by
  rw [value51, value55, value56, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (259 : Vertex) (274 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 92 = false := by
  rw [value54, value55, value56, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (273 : Vertex) (274 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 174 = true ∨ valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 92 = true := by
  rw [value54, value55, value56, value92, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(273 : Vertex), (274 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (259 : Vertex) [(273 : Vertex), (274 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 174 = true ∨ valuation q 51 = true ∨ valuation q 55 = true ∨ valuation q 92 = true := by
  rw [value51, value55, value56, value92, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (273 : Vertex) → w ∈ [(259 : Vertex), (274 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (273 : Vertex) [(259 : Vertex), (274 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = true ∨ valuation q 58 = true ∨ valuation q 60 = true := by
  rw [value53, value57, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ∈ [(272 : Vertex), (278 : Vertex), (284 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (276 : Vertex) [(272 : Vertex), (278 : Vertex), (284 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 175 = true ∨ valuation q 58 = true ∨ valuation q 60 = true := by
  rw [value57, value58, value60, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(278 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (272 : Vertex) [(278 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 175 = true ∨ valuation q 53 = true ∨ valuation q 60 = true := by
  rw [value53, value57, value60, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(272 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (278 : Vertex) [(272 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 175 = true ∨ valuation q 53 = true ∨ valuation q 58 = true := by
  rw [value53, value57, value58, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(272 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (284 : Vertex) [(272 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 7 = false ∨ valuation q 55 = false ∨ valuation q 61 = false := by
  rw [value7, value55, value58, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (274 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 7 = false ∨ valuation q 57 = false ∨ valuation q 61 = false := by
  rw [value7, value57, value58, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (276 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 7 = false ∨ valuation q 61 = false ∨ valuation q 94 = false := by
  rw [value7, value58, value61, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (286 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 61 = false := by
  rw [value55, value57, value58, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (274 : Vertex) (276 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 55 = false ∨ valuation q 61 = false ∨ valuation q 94 = false := by
  rw [value55, value58, value61, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (274 : Vertex) (286 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 94 = false := by
  rw [value57, value58, value61, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (276 : Vertex) (286 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 59 = true := by
  rw [value59, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (280 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 53 = true ∨ valuation q 60 = true ∨ valuation q 96 = true := by
  rw [value53, value59, value60, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ∈ [(272 : Vertex), (284 : Vertex), (408 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (280 : Vertex) [(272 : Vertex), (284 : Vertex), (408 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E007.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112007
