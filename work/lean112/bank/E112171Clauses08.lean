import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 180 = true ∨ valuation q 45 = true ∨ valuation q 65 = true ∨ valuation q 74 = true := by
  rw [value45, value65, value66, value74, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(257 : Vertex), (320 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (329 : Vertex) [(257 : Vertex), (320 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 180 = true ∨ valuation q 45 = true ∨ valuation q 65 = true ∨ valuation q 70 = true := by
  rw [value45, value65, value66, value70, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(257 : Vertex), (320 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (337 : Vertex) [(257 : Vertex), (320 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 49 = false ∨ valuation q 68 = false ∨ valuation q 77 = false := by
  rw [value49, value67, value68, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (262 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 181 = true ∨ valuation q 49 = true ∨ valuation q 77 = true := by
  rw [value49, value67, value77, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(262 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (327 : Vertex) [(262 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 68 = true := by
  rw [value68, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (327 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 67 = false ∨ valuation q 73 = false := by
  rw [value67, value73, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (327 : Vertex) (326 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 182 = true ∨ valuation q 67 = true ∨ valuation q 73 = true := by
  rw [value67, value68, value73, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(326 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (263 : Vertex) [(326 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 182 = true ∨ valuation q 50 = true ∨ valuation q 73 = true := by
  rw [value50, value68, value73, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(263 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (326 : Vertex) [(263 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 182 = true ∨ valuation q 50 = true ∨ valuation q 67 = true := by
  rw [value50, value67, value68, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(263 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (335 : Vertex) [(263 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 69 = true := by
  rw [value69, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (328 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 51 = true ∨ valuation q 65 = true ∨ valuation q 70 = true := by
  rw [value51, value65, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ∈ [(264 : Vertex), (320 : Vertex), (329 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (328 : Vertex) [(264 : Vertex), (320 : Vertex), (329 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 51 = false ∨ valuation q 65 = false := by
  rw [value51, value65, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (328 : Vertex) (264 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 51 = false ∨ valuation q 70 = false := by
  rw [value51, value70, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (328 : Vertex) (264 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 183 = true ∨ valuation q 65 = true ∨ valuation q 70 = true := by
  rw [value65, value69, value70, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(320 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (264 : Vertex) [(320 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 183 = true ∨ valuation q 51 = true ∨ valuation q 70 = true := by
  rw [value51, value69, value70, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(264 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (320 : Vertex) [(264 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 183 = true ∨ valuation q 51 = true ∨ valuation q 65 = true := by
  rw [value51, value65, value69, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(264 : Vertex), (320 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (329 : Vertex) [(264 : Vertex), (320 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 66 = false ∨ valuation q 69 = false ∨ valuation q 71 = false := by
  rw [value66, value69, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (328 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 66 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value66, value69, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (328 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 66 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value66, value70, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (331 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value69, value70, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (328 : Vertex) (331 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 184 = true ∨ valuation q 66 = true ∨ valuation q 71 = true ∨ valuation q 72 = true := by
  rw [value66, value70, value71, value72, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(321 : Vertex), (331 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (328 : Vertex) [(321 : Vertex), (331 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 184 = true ∨ valuation q 66 = true ∨ valuation q 69 = true ∨ valuation q 72 = true := by
  rw [value66, value69, value70, value72, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (331 : Vertex) → w ∈ [(321 : Vertex), (328 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (331 : Vertex) [(321 : Vertex), (328 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 184 = true ∨ valuation q 66 = true ∨ valuation q 69 = true ∨ valuation q 71 = true := by
  rw [value66, value69, value70, value71, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(321 : Vertex), (328 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (333 : Vertex) [(321 : Vertex), (328 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 71 = true := by
  rw [value71, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (331 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 53 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value53, value70, value71, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ∈ [(267 : Vertex), (329 : Vertex), (335 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (331 : Vertex) [(267 : Vertex), (329 : Vertex), (335 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 53 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value53, value70, value71, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (331 : Vertex) (267 : Vertex) (329 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 53 = false ∨ valuation q 70 = false := by
  rw [value53, value70, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (331 : Vertex) (267 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 53 = false ∨ valuation q 73 = false := by
  rw [value53, value73, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (331 : Vertex) (267 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 185 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value70, value71, value73, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(329 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (267 : Vertex) [(329 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 185 = true ∨ valuation q 53 = true ∨ valuation q 73 = true := by
  rw [value53, value71, value73, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(267 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (329 : Vertex) [(267 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 185 = true ∨ valuation q 53 = true ∨ valuation q 70 = true := by
  rw [value53, value70, value71, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(267 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (335 : Vertex) [(267 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 70 = true ∨ valuation q 73 = true ∨ valuation q 80 = true := by
  rw [value70, value72, value73, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ∈ [(329 : Vertex), (335 : Vertex), (349 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (333 : Vertex) [(329 : Vertex), (335 : Vertex), (349 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E171.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112171
