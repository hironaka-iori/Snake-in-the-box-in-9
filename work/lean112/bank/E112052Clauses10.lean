import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 53 = false ∨ valuation q 71 = false ∨ valuation q 112 = false := by
  rw [value53, value69, value71, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (327 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 53 = false ∨ valuation q 77 = false ∨ valuation q 112 = false := by
  rw [value53, value69, value77, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (341 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 68 = false ∨ valuation q 71 = false ∨ valuation q 77 = false := by
  rw [value68, value69, value71, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (324 : Vertex) (327 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 68 = false ∨ valuation q 71 = false ∨ valuation q 112 = false := by
  rw [value68, value69, value71, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (324 : Vertex) (327 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 68 = false ∨ valuation q 77 = false ∨ valuation q 112 = false := by
  rw [value68, value69, value77, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (324 : Vertex) (341 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 77 = false ∨ valuation q 112 = false := by
  rw [value69, value71, value77, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (327 : Vertex) (341 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 71 = false := by
  rw [value67, value68, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (322 : Vertex) (324 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 78 = false := by
  rw [value67, value68, value70, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (322 : Vertex) (324 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 67 = false ∨ valuation q 71 = false ∨ valuation q 78 = false := by
  rw [value67, value70, value71, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (322 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 68 = false ∨ valuation q 71 = false ∨ valuation q 78 = false := by
  rw [value68, value70, value71, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (324 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 197 = true ∨ valuation q 67 = true ∨ valuation q 68 = true ∨ valuation q 78 = true := by
  rw [value67, value68, value70, value78, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(322 : Vertex), (324 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (327 : Vertex) [(322 : Vertex), (324 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 197 = true ∨ valuation q 67 = true ∨ valuation q 68 = true ∨ valuation q 71 = true := by
  rw [value67, value68, value70, value71, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(322 : Vertex), (324 : Vertex), (327 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (342 : Vertex) [(322 : Vertex), (324 : Vertex), (327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 113 = false := by
  rw [value69, value70, value71, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (325 : Vertex) (326 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 69 = false ∨ valuation q 79 = false ∨ valuation q 113 = false := by
  rw [value69, value71, value79, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (325 : Vertex) (343 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 70 = false ∨ valuation q 79 = false ∨ valuation q 113 = false := by
  rw [value70, value71, value79, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (326 : Vertex) (343 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 198 = true ∨ valuation q 70 = true ∨ valuation q 79 = true ∨ valuation q 113 = true := by
  rw [value70, value71, value79, value113, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(326 : Vertex), (343 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (325 : Vertex) [(326 : Vertex), (343 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 198 = true ∨ valuation q 69 = true ∨ valuation q 79 = true ∨ valuation q 113 = true := by
  rw [value69, value71, value79, value113, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(325 : Vertex), (343 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (326 : Vertex) [(325 : Vertex), (343 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 198 = true ∨ valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 113 = true := by
  rw [value69, value70, value71, value113, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(325 : Vertex), (326 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (343 : Vertex) [(325 : Vertex), (326 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 198 = true ∨ valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 79 = true := by
  rw [value69, value70, value71, value79, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(325 : Vertex), (326 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (455 : Vertex) [(325 : Vertex), (326 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 80 = false := by
  rw [value72, value73, value74, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (330 : Vertex) (332 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 199 = true ∨ valuation q 74 = true ∨ valuation q 80 = true := by
  rw [value72, value74, value80, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(332 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (330 : Vertex) [(332 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 199 = true ∨ valuation q 73 = true ∨ valuation q 80 = true := by
  rw [value72, value73, value80, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(330 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (332 : Vertex) [(330 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 199 = true ∨ valuation q 73 = true ∨ valuation q 74 = true := by
  rw [value72, value73, value74, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(330 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (344 : Vertex) [(330 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 67 = false ∨ valuation q 72 = false ∨ valuation q 82 = false := by
  rw [value67, value72, value73, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (322 : Vertex) (328 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 200 = true ∨ valuation q 67 = true ∨ valuation q 82 = true := by
  rw [value67, value73, value82, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(322 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (328 : Vertex) [(322 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 200 = true ∨ valuation q 67 = true ∨ valuation q 72 = true := by
  rw [value67, value72, value73, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(322 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (346 : Vertex) [(322 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 3 = false ∨ valuation q 56 = false ∨ valuation q 68 = false := by
  rw [value3, value56, value68, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (76 : Vertex) (268 : Vertex) (324 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 3 = false ∨ valuation q 56 = false ∨ valuation q 72 = false := by
  rw [value3, value56, value72, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (76 : Vertex) (268 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 3 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value3, value68, value72, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (76 : Vertex) (324 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 56 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value56, value68, value72, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (268 : Vertex) (324 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 201 = true ∨ valuation q 3 = true ∨ valuation q 56 = true ∨ valuation q 68 = true := by
  rw [value3, value56, value68, value74, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(76 : Vertex), (268 : Vertex), (324 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (328 : Vertex) [(76 : Vertex), (268 : Vertex), (324 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 202 = true ∨ valuation q 81 = true := by
  rw [value75, value81, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(345 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (341 : Vertex) [(345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E052.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112052
