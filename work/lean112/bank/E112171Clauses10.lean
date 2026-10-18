import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value77, value78, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (342 : Vertex) (346 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 195 = true ∨ valuation q 78 = true ∨ valuation q 79 = true := by
  rw [value78, value79, value81, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(346 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (342 : Vertex) [(346 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 195 = true ∨ valuation q 77 = true ∨ valuation q 79 = true := by
  rw [value77, value79, value81, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(342 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (346 : Vertex) [(342 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 195 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value77, value78, value81, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(342 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (348 : Vertex) [(342 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 11 = false ∨ valuation q 44 = false ∨ valuation q 86 = false := by
  rw [value11, value44, value82, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (128 : Vertex) (256 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 11 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value11, value82, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (128 : Vertex) (385 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 44 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value44, value82, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (256 : Vertex) (385 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 196 = true ∨ valuation q 11 = true ∨ valuation q 44 = true ∨ valuation q 83 = true := by
  rw [value11, value44, value82, value83, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(128 : Vertex), (256 : Vertex), (385 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (392 : Vertex) [(128 : Vertex), (256 : Vertex), (385 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 45 = true ∨ valuation q 82 = true ∨ valuation q 87 = true ∨ valuation q 91 = true := by
  rw [value45, value82, value83, value87, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ∈ [(257 : Vertex), (384 : Vertex), (393 : Vertex), (401 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (385 : Vertex) [(257 : Vertex), (384 : Vertex), (393 : Vertex), (401 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 45 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value45, value83, value87, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (257 : Vertex) (393 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 82 = false ∨ valuation q 91 = false := by
  rw [value82, value91, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (385 : Vertex) (384 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value87, value91, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (385 : Vertex) (393 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 197 = true ∨ valuation q 45 = true ∨ valuation q 87 = true ∨ valuation q 91 = true := by
  rw [value45, value83, value87, value91, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(257 : Vertex), (393 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (384 : Vertex) [(257 : Vertex), (393 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 197 = true ∨ valuation q 45 = true ∨ valuation q 82 = true ∨ valuation q 91 = true := by
  rw [value45, value82, value83, value91, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(257 : Vertex), (384 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (393 : Vertex) [(257 : Vertex), (384 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 197 = true ∨ valuation q 45 = true ∨ valuation q 82 = true ∨ valuation q 87 = true := by
  rw [value45, value82, value83, value87, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(257 : Vertex), (384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (401 : Vertex) [(257 : Vertex), (384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 49 = false ∨ valuation q 85 = false := by
  rw [value14, value49, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (134 : Vertex) (262 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 49 = false ∨ valuation q 85 = false ∨ valuation q 94 = false := by
  rw [value49, value84, value85, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (262 : Vertex) (391 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 199 = true ∨ valuation q 50 = true ∨ valuation q 84 = true ∨ valuation q 90 = true := by
  rw [value50, value84, value85, value90, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(263 : Vertex), (390 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (135 : Vertex) [(263 : Vertex), (390 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 199 = true ∨ valuation q 15 = true ∨ valuation q 50 = true ∨ valuation q 90 = true := by
  rw [value15, value50, value85, value90, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(135 : Vertex), (263 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (390 : Vertex) [(135 : Vertex), (263 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 16 = true ∨ valuation q 51 = true ∨ valuation q 82 = true ∨ valuation q 87 = true := by
  rw [value16, value51, value82, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ∈ [(136 : Vertex), (264 : Vertex), (384 : Vertex), (393 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (392 : Vertex) [(136 : Vertex), (264 : Vertex), (384 : Vertex), (393 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 200 = true ∨ valuation q 51 = true ∨ valuation q 82 = true ∨ valuation q 87 = true := by
  rw [value51, value82, value86, value87, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(264 : Vertex), (384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (136 : Vertex) [(264 : Vertex), (384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 200 = true ∨ valuation q 16 = true ∨ valuation q 82 = true ∨ valuation q 87 = true := by
  rw [value16, value82, value86, value87, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(136 : Vertex), (384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (264 : Vertex) [(136 : Vertex), (384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 200 = true ∨ valuation q 16 = true ∨ valuation q 51 = true ∨ valuation q 87 = true := by
  rw [value16, value51, value86, value87, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(136 : Vertex), (264 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (384 : Vertex) [(136 : Vertex), (264 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 17 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value17, value83, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (385 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 17 = false ∨ valuation q 86 = false ∨ valuation q 88 = false := by
  rw [value17, value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (392 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 17 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value17, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (392 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 17 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value17, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (395 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 88 = false := by
  rw [value83, value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (385 : Vertex) (392 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value83, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (385 : Vertex) (392 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 83 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value83, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (385 : Vertex) (395 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value86, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (392 : Vertex) (395 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 53 = true ∨ valuation q 87 = true ∨ valuation q 90 = true := by
  rw [value53, value87, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ∈ [(267 : Vertex), (393 : Vertex), (399 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (395 : Vertex) [(267 : Vertex), (393 : Vertex), (399 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E171.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112171
