import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 163 = true ∨ valuation q 23 = true ∨ valuation q 40 = true := by
  rw [value23, value40, value41, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (319 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(287 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (319 : Vertex) (447 : Vertex) [(287 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 52 = false := by
  rw [value42, value43, value44, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (328 : Vertex) (352 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 102 = false := by
  rw [value42, value43, value44, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (328 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 52 = false ∨ valuation q 102 = false := by
  rw [value42, value43, value52, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (352 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value43, value44, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (320 : Vertex) (321 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 46 = false := by
  rw [value1, value6, value43, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (65 : Vertex) (257 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 53 = false := by
  rw [value1, value6, value43, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (65 : Vertex) (257 : Vertex) (353 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 6 = false ∨ valuation q 46 = false ∨ valuation q 53 = false := by
  rw [value6, value43, value46, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (257 : Vertex) (337 : Vertex) (353 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 165 = true ∨ valuation q 1 = true ∨ valuation q 42 = true ∨ valuation q 46 = true ∨ valuation q 53 = true := by
  rw [value1, value42, value43, value46, value53, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(65 : Vertex), (320 : Vertex), (337 : Vertex), (353 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (257 : Vertex) [(65 : Vertex), (320 : Vertex), (337 : Vertex), (353 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 165 = true ∨ valuation q 1 = true ∨ valuation q 6 = true ∨ valuation q 42 = true ∨ valuation q 46 = true := by
  rw [value1, value6, value42, value43, value46, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (353 : Vertex) → w ∈ [(65 : Vertex), (257 : Vertex), (320 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (353 : Vertex) [(65 : Vertex), (257 : Vertex), (320 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 10 = false ∨ valuation q 42 = false ∨ valuation q 48 = false := by
  rw [value10, value42, value44, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (264 : Vertex) (320 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 10 = false ∨ valuation q 45 = false ∨ valuation q 48 = false := by
  rw [value10, value44, value45, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (264 : Vertex) (330 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 167 = true ∨ valuation q 44 = true := by
  rw [value44, value45, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (362 : Vertex) → w ∈ [(328 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (362 : Vertex) [(328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 15 = false ∨ valuation q 43 = false ∨ valuation q 47 = false := by
  rw [value15, value43, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (337 : Vertex) (273 : Vertex) (321 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 43 = false ∨ valuation q 47 = false := by
  rw [value43, value47, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (337 : Vertex) (321 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 168 = true ∨ valuation q 15 = true ∨ valuation q 43 = true := by
  rw [value15, value43, value46, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(273 : Vertex), (321 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (341 : Vertex) [(273 : Vertex), (321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 46 = true ∨ valuation q 106 = true := by
  rw [value46, value47, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ∈ [(337 : Vertex), (469 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (341 : Vertex) [(337 : Vertex), (469 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 47 = true := by
  rw [value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 44 = false ∨ valuation q 50 = false := by
  rw [value44, value50, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (344 : Vertex) (328 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 170 = true ∨ valuation q 44 = true ∨ valuation q 107 = true := by
  rw [value44, value48, value107, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (344 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(328 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (344 : Vertex) (348 : Vertex) [(328 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 51 = false ∨ valuation q 61 = false := by
  rw [value51, value61, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (347 : Vertex) (351 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 171 = true ∨ valuation q 61 = true := by
  rw [value49, value61, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (351 : Vertex) → w ∈ [(379 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (351 : Vertex) [(379 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 171 = true ∨ valuation q 51 = true := by
  rw [value49, value51, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(351 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (379 : Vertex) [(351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 172 = true ∨ valuation q 62 = true := by
  rw [value50, value62, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(380 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (344 : Vertex) [(380 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 172 = true ∨ valuation q 48 = true := by
  rw [value48, value50, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (380 : Vertex) → w ∈ [(344 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (380 : Vertex) [(344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 23 = false ∨ valuation q 49 = false ∨ valuation q 109 = false := by
  rw [value23, value49, value51, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (287 : Vertex) (347 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 173 = true ∨ valuation q 23 = true ∨ valuation q 109 = true := by
  rw [value23, value51, value109, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(287 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (347 : Vertex) [(287 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 173 = true ∨ valuation q 23 = true ∨ valuation q 49 = true := by
  rw [value23, value49, value51, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(287 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (479 : Vertex) [(287 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 24 = false ∨ valuation q 56 = false ∨ valuation q 59 = false := by
  rw [value24, value52, value56, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (352 : Vertex) (288 : Vertex) (356 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 42 = false ∨ valuation q 56 = false ∨ valuation q 59 = false := by
  rw [value42, value52, value56, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (352 : Vertex) (320 : Vertex) (356 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 42 = false ∨ valuation q 57 = false ∨ valuation q 59 = false := by
  rw [value42, value52, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (352 : Vertex) (320 : Vertex) (360 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 57 = false := by
  rw [value52, value53, value54, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (352 : Vertex) (353 : Vertex) (354 : Vertex) (360 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E258.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112258
