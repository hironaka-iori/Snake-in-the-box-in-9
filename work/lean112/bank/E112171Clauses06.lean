import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 71 = false ∨ valuation q 88 = false := by
  rw [value53, value56, value71, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (271 : Vertex) (331 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 63 = false ∨ valuation q 71 = false ∨ valuation q 88 = false := by
  rw [value53, value63, value71, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (283 : Vertex) (331 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 54 = true := by
  rw [value54, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (268 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 47 = true ∨ valuation q 51 = true ∨ valuation q 55 = true := by
  rw [value47, value51, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ∈ [(260 : Vertex), (264 : Vertex), (270 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (268 : Vertex) [(260 : Vertex), (264 : Vertex), (270 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 47 = false ∨ valuation q 51 = false := by
  rw [value47, value51, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (268 : Vertex) (260 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 51 = false ∨ valuation q 55 = false := by
  rw [value51, value55, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (268 : Vertex) (264 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 168 = true ∨ valuation q 51 = true ∨ valuation q 55 = true := by
  rw [value51, value54, value55, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(264 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (260 : Vertex) [(264 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 168 = true ∨ valuation q 47 = true ∨ valuation q 55 = true := by
  rw [value47, value54, value55, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(260 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (264 : Vertex) [(260 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 168 = true ∨ valuation q 47 = true ∨ valuation q 51 = true := by
  rw [value47, value51, value54, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(260 : Vertex), (264 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (270 : Vertex) [(260 : Vertex), (264 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value49, value52, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (262 : Vertex) (266 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 56 = false := by
  rw [value49, value52, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (262 : Vertex) (266 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value49, value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (262 : Vertex) (268 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value52, value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (266 : Vertex) (268 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 169 = true ∨ valuation q 49 = true ∨ valuation q 52 = true ∨ valuation q 56 = true := by
  rw [value49, value52, value55, value56, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(262 : Vertex), (266 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (268 : Vertex) [(262 : Vertex), (266 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 6 = false ∨ valuation q 50 = false ∨ valuation q 53 = false := by
  rw [value6, value50, value53, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 6 = false ∨ valuation q 50 = false ∨ valuation q 64 = false := by
  rw [value6, value50, value56, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 6 = false ∨ valuation q 50 = false ∨ valuation q 73 = false := by
  rw [value6, value50, value56, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 6 = false ∨ valuation q 53 = false ∨ valuation q 73 = false := by
  rw [value6, value53, value56, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (267 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 73 = false := by
  rw [value50, value53, value56, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 50 = false ∨ valuation q 55 = false ∨ valuation q 73 = false := by
  rw [value50, value55, value56, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (270 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 53 = false ∨ valuation q 64 = false ∨ valuation q 73 = false := by
  rw [value53, value56, value64, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (287 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 53 = false ∨ valuation q 73 = false ∨ valuation q 90 = false := by
  rw [value53, value56, value73, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (335 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 64 = false ∨ valuation q 73 = false ∨ valuation q 90 = false := by
  rw [value56, value64, value73, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (287 : Vertex) (335 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 45 = false ∨ valuation q 59 = false ∨ valuation q 74 = false := by
  rw [value45, value57, value59, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (257 : Vertex) (277 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 59 = false ∨ valuation q 61 = false ∨ valuation q 74 = false := by
  rw [value57, value59, value61, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (277 : Vertex) (281 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 59 = false ∨ valuation q 74 = false ∨ valuation q 91 = false := by
  rw [value57, value59, value74, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (277 : Vertex) (337 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 58 = true := by
  rw [value58, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (276 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 47 = true ∨ valuation q 59 = true := by
  rw [value47, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ∈ [(260 : Vertex), (277 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (276 : Vertex) [(260 : Vertex), (277 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 47 = false ∨ valuation q 59 = false := by
  rw [value47, value59, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (276 : Vertex) (260 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 172 = true ∨ valuation q 59 = true := by
  rw [value58, value59, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(277 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (260 : Vertex) [(277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 172 = true ∨ valuation q 47 = true := by
  rw [value47, value58, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(260 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (277 : Vertex) [(260 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 48 = false ∨ valuation q 57 = false ∨ valuation q 58 = false := by
  rw [value48, value57, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (261 : Vertex) (273 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E171.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112171
