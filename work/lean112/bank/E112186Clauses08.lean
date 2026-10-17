import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 194 = true ∨ valuation q 53 = true ∨ valuation q 67 = true ∨ valuation q 72 = true := by
  rw [value53, value67, value70, value72, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(267 : Vertex), (323 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (75 : Vertex) [(267 : Vertex), (323 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 194 = true ∨ valuation q 4 = true ∨ valuation q 67 = true ∨ valuation q 72 = true := by
  rw [value4, value67, value70, value72, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(75 : Vertex), (323 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (267 : Vertex) [(75 : Vertex), (323 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 194 = true ∨ valuation q 4 = true ∨ valuation q 53 = true ∨ valuation q 67 = true := by
  rw [value4, value53, value67, value70, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(75 : Vertex), (267 : Vertex), (323 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (335 : Vertex) [(75 : Vertex), (267 : Vertex), (323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 68 = false ∨ valuation q 72 = false ∨ valuation q 79 = false := by
  rw [value68, value71, value72, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (325 : Vertex) (335 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 72 = true ∨ valuation q 79 = true := by
  rw [value71, value72, value79, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(335 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (325 : Vertex) [(335 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 68 = true ∨ valuation q 79 = true := by
  rw [value68, value71, value79, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(325 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (335 : Vertex) [(325 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 68 = true ∨ valuation q 72 = true := by
  rw [value68, value71, value72, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(325 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (349 : Vertex) [(325 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 81 = false := by
  rw [value70, value71, value72, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (335 : Vertex) (331 : Vertex) (333 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 196 = true ∨ valuation q 70 = true ∨ valuation q 81 = true := by
  rw [value70, value72, value81, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(331 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (333 : Vertex) [(331 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 65 = false ∨ valuation q 75 = false := by
  rw [value65, value75, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (337 : Vertex) (321 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 197 = true ∨ valuation q 75 = true := by
  rw [value73, value75, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(339 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (321 : Vertex) [(339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 197 = true ∨ valuation q 65 = true := by
  rw [value65, value73, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(321 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (339 : Vertex) [(321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 66 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value66, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (322 : Vertex) (339 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 66 = true ∨ valuation q 75 = true := by
  rw [value66, value74, value75, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(322 : Vertex), (339 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (342 : Vertex) [(322 : Vertex), (339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 199 = true ∨ valuation q 73 = true ∨ valuation q 74 = true := by
  rw [value73, value74, value75, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(337 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (323 : Vertex) [(337 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 199 = true ∨ valuation q 67 = true ∨ valuation q 74 = true := by
  rw [value67, value74, value75, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(323 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (337 : Vertex) [(323 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 199 = true ∨ valuation q 67 = true ∨ valuation q 73 = true := by
  rw [value67, value73, value75, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(323 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (338 : Vertex) [(323 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 80 = true := by
  rw [value76, value80, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(350 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (338 : Vertex) [(350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 74 = true := by
  rw [value74, value76, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(338 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (350 : Vertex) [(338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 60 = false ∨ valuation q 69 = false ∨ valuation q 78 = false := by
  rw [value60, value69, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (280 : Vertex) (328 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 79 = true ∨ valuation q 80 = true := by
  rw [value78, value79, value80, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(349 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (344 : Vertex) [(349 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 77 = true ∨ valuation q 80 = true := by
  rw [value77, value78, value80, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(344 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (349 : Vertex) [(344 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 77 = true ∨ valuation q 79 = true := by
  rw [value77, value78, value79, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(344 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (350 : Vertex) [(344 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 71 = false ∨ valuation q 78 = false ∨ valuation q 81 = false := by
  rw [value71, value78, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (333 : Vertex) (348 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 71 = false ∨ valuation q 78 = false ∨ valuation q 123 = false := by
  rw [value71, value78, value79, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (333 : Vertex) (348 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 71 = false ∨ valuation q 81 = false ∨ valuation q 123 = false := by
  rw [value71, value79, value81, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (333 : Vertex) (351 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 81 = false := by
  rw [value76, value78, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (342 : Vertex) (348 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 11 = false ∨ valuation q 63 = false ∨ valuation q 72 = false := by
  rw [value11, value63, value72, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (95 : Vertex) (287 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 11 = false ∨ valuation q 72 = false ∨ valuation q 79 = false := by
  rw [value11, value72, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (95 : Vertex) (335 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 11 = false ∨ valuation q 72 = false ∨ valuation q 80 = false := by
  rw [value11, value72, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (95 : Vertex) (335 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 63 = false ∨ valuation q 72 = false ∨ valuation q 79 = false := by
  rw [value63, value72, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (287 : Vertex) (335 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 63 = false ∨ valuation q 72 = false ∨ valuation q 80 = false := by
  rw [value63, value72, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (287 : Vertex) (335 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E186.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112186
