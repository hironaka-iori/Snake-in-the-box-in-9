import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 35 = false ∨ valuation q 42 = false ∨ valuation q 122 = false := by
  rw [value35, value42, value44, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (199 : Vertex) (213 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 35 = false ∨ valuation q 43 = false ∨ valuation q 122 = false := by
  rw [value35, value43, value44, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (199 : Vertex) (214 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 122 = false := by
  rw [value42, value43, value44, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (213 : Vertex) (214 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 171 = true ∨ valuation q 7 = true ∨ valuation q 35 = true ∨ valuation q 42 = true ∨ valuation q 43 = true ∨ valuation q 122 = true := by
  rw [value7, value35, value42, value43, value44, value122, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(87 : Vertex), (199 : Vertex), (213 : Vertex), (214 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (151 : Vertex) [(87 : Vertex), (199 : Vertex), (213 : Vertex), (214 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 171 = true ∨ valuation q 7 = true ∨ valuation q 27 = true ∨ valuation q 35 = true ∨ valuation q 43 = true ∨ valuation q 122 = true := by
  rw [value7, value27, value35, value43, value44, value122, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(87 : Vertex), (151 : Vertex), (199 : Vertex), (214 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (213 : Vertex) [(87 : Vertex), (151 : Vertex), (199 : Vertex), (214 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 171 = true ∨ valuation q 7 = true ∨ valuation q 27 = true ∨ valuation q 35 = true ∨ valuation q 42 = true ∨ valuation q 122 = true := by
  rw [value7, value27, value35, value42, value44, value122, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(87 : Vertex), (151 : Vertex), (199 : Vertex), (213 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (214 : Vertex) [(87 : Vertex), (151 : Vertex), (199 : Vertex), (213 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 172 = true ∨ valuation q 47 = true ∨ valuation q 48 = true := by
  rw [value45, value47, value48, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(219 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (209 : Vertex) [(219 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 172 = true ∨ valuation q 40 = true ∨ valuation q 48 = true := by
  rw [value40, value45, value48, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(209 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (219 : Vertex) [(209 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 172 = true ∨ valuation q 40 = true ∨ valuation q 47 = true := by
  rw [value40, value45, value47, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(209 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (221 : Vertex) [(209 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 37 = false ∨ valuation q 47 = false ∨ valuation q 124 = false := by
  rw [value37, value46, value47, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (202 : Vertex) (219 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 173 = true ∨ valuation q 47 = true ∨ valuation q 124 = true := by
  rw [value46, value47, value124, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(219 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (202 : Vertex) [(219 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 173 = true ∨ valuation q 37 = true ∨ valuation q 124 = true := by
  rw [value37, value46, value124, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(202 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (219 : Vertex) [(202 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 47 = true := by
  rw [value47, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (219 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 45 = true ∨ valuation q 46 = true := by
  rw [value45, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ∈ [(217 : Vertex), (218 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (219 : Vertex) [(217 : Vertex), (218 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 45 = false ∨ valuation q 46 = false := by
  rw [value45, value46, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (219 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 174 = true ∨ valuation q 46 = true := by
  rw [value46, value47, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(218 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (217 : Vertex) [(218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 174 = true ∨ valuation q 45 = true := by
  rw [value45, value47, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(217 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (218 : Vertex) [(217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 126 = false := by
  rw [value42, value45, value48, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (213 : Vertex) (217 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value49, value51, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (259 : Vertex) (261 : Vertex) (265 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value53, value54, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (257 : Vertex) (261 : Vertex) (265 : Vertex) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 176 = true ∨ valuation q 53 = true ∨ valuation q 54 = true := by
  rw [value49, value53, value54, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(261 : Vertex), (265 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (259 : Vertex) [(261 : Vertex), (265 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 176 = true ∨ valuation q 51 = true ∨ valuation q 54 = true := by
  rw [value49, value51, value54, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(259 : Vertex), (265 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (261 : Vertex) [(259 : Vertex), (265 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 176 = true ∨ valuation q 51 = true ∨ valuation q 53 = true := by
  rw [value49, value51, value53, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(259 : Vertex), (261 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (265 : Vertex) [(259 : Vertex), (261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 67 = false := by
  rw [value50, value51, value60, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (274 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 86 = false := by
  rw [value50, value51, value60, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (274 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 67 = false ∨ valuation q 86 = false := by
  rw [value50, value51, value67, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 60 = false ∨ valuation q 67 = false ∨ valuation q 86 = false := by
  rw [value50, value60, value67, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (274 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 177 = true ∨ valuation q 60 = true ∨ valuation q 67 = true ∨ valuation q 86 = true := by
  rw [value50, value60, value67, value86, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(274 : Vertex), (322 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (259 : Vertex) [(274 : Vertex), (322 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value49, value50, value51, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (259 : Vertex) (257 : Vertex) (258 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 61 = false := by
  rw [value49, value50, value51, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (259 : Vertex) (257 : Vertex) (258 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 55 = false ∨ valuation q 61 = false := by
  rw [value49, value51, value55, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (259 : Vertex) (257 : Vertex) (267 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 55 = false ∨ valuation q 61 = false := by
  rw [value50, value51, value55, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (259 : Vertex) (258 : Vertex) (267 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E052.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112052
