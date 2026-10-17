import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 189 = true ∨ valuation q 64 = true ∨ valuation q 69 = true ∨ valuation q 107 = true := by
  rw [value64, value68, value69, value107, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(324 : Vertex), (334 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (328 : Vertex) [(324 : Vertex), (334 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 189 = true ∨ valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 107 = true := by
  rw [value64, value66, value68, value107, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(324 : Vertex), (328 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (334 : Vertex) [(324 : Vertex), (328 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 69 = true := by
  rw [value69, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (334 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 65 = true ∨ valuation q 68 = true ∨ valuation q 109 = true := by
  rw [value65, value68, value69, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ∈ [(326 : Vertex), (332 : Vertex), (462 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (334 : Vertex) [(326 : Vertex), (332 : Vertex), (462 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 109 = false := by
  rw [value65, value68, value69, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (334 : Vertex) (326 : Vertex) (332 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 65 = false ∨ valuation q 109 = false := by
  rw [value65, value109, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (334 : Vertex) (326 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 68 = false ∨ valuation q 109 = false := by
  rw [value68, value109, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (334 : Vertex) (332 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 190 = true ∨ valuation q 68 = true ∨ valuation q 109 = true := by
  rw [value68, value69, value109, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(332 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (326 : Vertex) [(332 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 190 = true ∨ valuation q 65 = true ∨ valuation q 109 = true := by
  rw [value65, value69, value109, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(326 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (332 : Vertex) [(326 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 190 = true ∨ valuation q 65 = true ∨ valuation q 68 = true := by
  rw [value65, value68, value69, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(326 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (462 : Vertex) [(326 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 76 = false ∨ valuation q 113 = false := by
  rw [value70, value72, value76, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (342 : Vertex) (346 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 191 = true ∨ valuation q 76 = true ∨ valuation q 113 = true := by
  rw [value70, value76, value113, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(346 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (342 : Vertex) [(346 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 191 = true ∨ valuation q 72 = true ∨ valuation q 113 = true := by
  rw [value70, value72, value113, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(342 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (346 : Vertex) [(342 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 191 = true ∨ valuation q 72 = true ∨ valuation q 76 = true := by
  rw [value70, value72, value76, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(342 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (466 : Vertex) [(342 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 71 = true := by
  rw [value71, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (341 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 73 = true ∨ valuation q 78 = true := by
  rw [value71, value73, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ∈ [(343 : Vertex), (349 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (341 : Vertex) [(343 : Vertex), (349 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 192 = true ∨ valuation q 78 = true := by
  rw [value71, value78, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(349 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (343 : Vertex) [(349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 192 = true ∨ valuation q 73 = true := by
  rw [value71, value73, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(343 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (349 : Vertex) [(343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 72 = true := by
  rw [value72, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (342 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 65 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value65, value70, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ∈ [(326 : Vertex), (338 : Vertex), (343 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (342 : Vertex) [(326 : Vertex), (338 : Vertex), (343 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 65 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value65, value70, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (326 : Vertex) (338 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 193 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value70, value72, value73, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(338 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (326 : Vertex) [(338 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 193 = true ∨ valuation q 65 = true ∨ valuation q 73 = true := by
  rw [value65, value72, value73, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(326 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (338 : Vertex) [(326 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 193 = true ∨ valuation q 65 = true ∨ valuation q 70 = true := by
  rw [value65, value70, value72, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(326 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (343 : Vertex) [(326 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 194 = true ∨ valuation q 72 = true := by
  rw [value72, value73, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(342 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (341 : Vertex) [(342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 194 = true ∨ valuation q 71 = true := by
  rw [value71, value73, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(341 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (342 : Vertex) [(341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 19 = false ∨ valuation q 66 = false ∨ valuation q 75 = false := by
  rw [value19, value66, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (328 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 19 = false ∨ valuation q 66 = false ∨ valuation q 76 = false := by
  rw [value19, value66, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (328 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 19 = false ∨ valuation q 66 = false ∨ valuation q 116 = false := by
  rw [value19, value66, value74, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (328 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 19 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value19, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (345 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 19 = false ∨ valuation q 75 = false ∨ valuation q 116 = false := by
  rw [value19, value74, value75, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (345 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 19 = false ∨ valuation q 76 = false ∨ valuation q 116 = false := by
  rw [value19, value74, value76, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (346 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E019.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112019
