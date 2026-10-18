import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 165 = true ∨ valuation q 53 = true := by
  rw [value43, value53, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (323 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(355 : Vertex)] := by decide
  have hg := other_cover q (323 : Vertex) (327 : Vertex) [(355 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 165 = true ∨ valuation q 45 = true := by
  rw [value43, value45, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (323 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(327 : Vertex)] := by decide
  have hg := other_cover q (323 : Vertex) (355 : Vertex) [(327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 166 = true ∨ valuation q 54 = true := by
  rw [value44, value54, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(356 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (320 : Vertex) [(356 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 166 = true ∨ valuation q 42 = true := by
  rw [value42, value44, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(320 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (356 : Vertex) [(320 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 10 = false ∨ valuation q 43 = false ∨ valuation q 104 = false := by
  rw [value10, value43, value45, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (263 : Vertex) (323 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 167 = true ∨ valuation q 10 = true ∨ valuation q 104 = true := by
  rw [value10, value45, value104, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(263 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (323 : Vertex) [(263 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 167 = true ∨ valuation q 10 = true ∨ valuation q 43 = true := by
  rw [value10, value43, value45, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(263 : Vertex), (323 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (455 : Vertex) [(263 : Vertex), (323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 12 = false ∨ valuation q 47 = false ∨ valuation q 51 = false := by
  rw [value12, value46, value47, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (265 : Vertex) (333 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 47 = false ∨ valuation q 51 = false := by
  rw [value47, value51, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (329 : Vertex) (333 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 168 = true ∨ valuation q 12 = true ∨ valuation q 51 = true := by
  rw [value12, value46, value51, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(265 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (333 : Vertex) [(265 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 46 = true ∨ valuation q 106 = true := by
  rw [value46, value47, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ∈ [(329 : Vertex), (461 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (333 : Vertex) [(329 : Vertex), (461 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 47 = true := by
  rw [value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 16 = false ∨ valuation q 42 = false ∨ valuation q 49 = false := by
  rw [value16, value42, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (272 : Vertex) (320 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 16 = false ∨ valuation q 42 = false ∨ valuation q 50 = false := by
  rw [value16, value42, value48, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (272 : Vertex) (320 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 42 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value42, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (320 : Vertex) (338 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 48 = false ∨ valuation q 58 = false := by
  rw [value48, value58, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (338 : Vertex) (336 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 171 = true ∨ valuation q 58 = true := by
  rw [value49, value58, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (336 : Vertex) → w ∈ [(370 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (336 : Vertex) [(370 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 171 = true ∨ valuation q 48 = true := by
  rw [value48, value49, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (370 : Vertex) → w ∈ [(336 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (370 : Vertex) [(336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 59 = false := by
  rw [value48, value50, value51, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (336 : Vertex) (345 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 108 = false := by
  rw [value48, value50, value51, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (336 : Vertex) (345 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 48 = false ∨ valuation q 51 = false := by
  rw [value48, value51, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (344 : Vertex) (336 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 1 = false ∨ valuation q 20 = false ∨ valuation q 46 = false := by
  rw [value1, value20, value46, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (89 : Vertex) (281 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 1 = false ∨ valuation q 20 = false ∨ valuation q 50 = false := by
  rw [value1, value20, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (89 : Vertex) (281 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 1 = false ∨ valuation q 20 = false ∨ valuation q 60 = false := by
  rw [value1, value20, value51, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (89 : Vertex) (281 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 1 = false ∨ valuation q 46 = false ∨ valuation q 60 = false := by
  rw [value1, value46, value51, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (89 : Vertex) (329 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 173 = true ∨ valuation q 20 = true ∨ valuation q 46 = true ∨ valuation q 50 = true ∨ valuation q 60 = true := by
  rw [value20, value46, value50, value51, value60, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(281 : Vertex), (329 : Vertex), (344 : Vertex), (377 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (89 : Vertex) [(281 : Vertex), (329 : Vertex), (344 : Vertex), (377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 173 = true ∨ valuation q 1 = true ∨ valuation q 20 = true ∨ valuation q 46 = true ∨ valuation q 60 = true := by
  rw [value1, value20, value46, value51, value60, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(89 : Vertex), (281 : Vertex), (329 : Vertex), (377 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (344 : Vertex) [(89 : Vertex), (281 : Vertex), (329 : Vertex), (377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 173 = true ∨ valuation q 1 = true ∨ valuation q 20 = true ∨ valuation q 46 = true ∨ valuation q 50 = true := by
  rw [value1, value20, value46, value50, value51, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(89 : Vertex), (281 : Vertex), (329 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (377 : Vertex) [(89 : Vertex), (281 : Vertex), (329 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 174 = true ∨ valuation q 110 = true := by
  rw [value52, value110, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (353 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(481 : Vertex)] := by decide
  have hg := other_cover q (353 : Vertex) (355 : Vertex) [(481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 174 = true ∨ valuation q 53 = true := by
  rw [value52, value53, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (353 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(355 : Vertex)] := by decide
  have hg := other_cover q (353 : Vertex) (481 : Vertex) [(355 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 175 = true ∨ valuation q 52 = true := by
  rw [value52, value53, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(353 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (323 : Vertex) [(353 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 175 = true ∨ valuation q 43 = true := by
  rw [value43, value53, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (353 : Vertex) → w ∈ [(323 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (353 : Vertex) [(323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E254.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112254
