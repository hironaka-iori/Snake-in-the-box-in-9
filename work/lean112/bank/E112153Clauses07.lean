import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 70 = true ∨ valuation q 109 = true := by
  rw [value70, value71, value109, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(328 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (345 : Vertex) [(328 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 70 = true ∨ valuation q 78 = true := by
  rw [value70, value71, value78, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(328 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (457 : Vertex) [(328 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 68 = false ∨ valuation q 73 = false ∨ valuation q 81 = false := by
  rw [value68, value72, value73, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (334 : Vertex) (326 : Vertex) (335 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 68 = false ∨ valuation q 73 = false ∨ valuation q 113 = false := by
  rw [value68, value72, value73, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (334 : Vertex) (326 : Vertex) (335 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 68 = false ∨ valuation q 81 = false ∨ valuation q 113 = false := by
  rw [value68, value72, value81, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (334 : Vertex) (326 : Vertex) (350 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 73 = false ∨ valuation q 81 = false ∨ valuation q 113 = false := by
  rw [value72, value73, value81, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (334 : Vertex) (335 : Vertex) (350 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 68 = false ∨ valuation q 73 = false := by
  rw [value68, value73, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (334 : Vertex) (326 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 196 = true ∨ valuation q 73 = true ∨ valuation q 81 = true ∨ valuation q 113 = true := by
  rw [value72, value73, value81, value113, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(335 : Vertex), (350 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (326 : Vertex) [(335 : Vertex), (350 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 196 = true ∨ valuation q 68 = true ∨ valuation q 81 = true ∨ valuation q 113 = true := by
  rw [value68, value72, value81, value113, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(326 : Vertex), (350 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (335 : Vertex) [(326 : Vertex), (350 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 197 = true ∨ valuation q 69 = true ∨ valuation q 72 = true ∨ valuation q 114 = true := by
  rw [value69, value72, value73, value114, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(327 : Vertex), (334 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (271 : Vertex) [(327 : Vertex), (334 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 197 = true ∨ valuation q 56 = true ∨ valuation q 72 = true ∨ valuation q 114 = true := by
  rw [value56, value72, value73, value114, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(271 : Vertex), (334 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (327 : Vertex) [(271 : Vertex), (334 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 197 = true ∨ valuation q 56 = true ∨ valuation q 69 = true ∨ valuation q 114 = true := by
  rw [value56, value69, value73, value114, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(271 : Vertex), (327 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (334 : Vertex) [(271 : Vertex), (327 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 197 = true ∨ valuation q 56 = true ∨ valuation q 69 = true ∨ valuation q 72 = true := by
  rw [value56, value69, value72, value73, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(271 : Vertex), (327 : Vertex), (334 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (463 : Vertex) [(271 : Vertex), (327 : Vertex), (334 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value74, value76, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (337 : Vertex) (339 : Vertex) (341 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value74, value77, value78, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(341 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (339 : Vertex) [(341 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 76 = true ∨ valuation q 78 = true := by
  rw [value74, value76, value78, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(339 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (341 : Vertex) [(339 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 76 = true ∨ valuation q 77 = true := by
  rw [value74, value76, value77, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(339 : Vertex), (341 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (345 : Vertex) [(339 : Vertex), (341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 199 = true ∨ valuation q 66 = true ∨ valuation q 76 = true := by
  rw [value66, value75, value76, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(322 : Vertex), (339 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (274 : Vertex) [(322 : Vertex), (339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 199 = true ∨ valuation q 58 = true ∨ valuation q 76 = true := by
  rw [value58, value75, value76, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(274 : Vertex), (339 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (322 : Vertex) [(274 : Vertex), (339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 199 = true ∨ valuation q 58 = true ∨ valuation q 66 = true := by
  rw [value58, value66, value75, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(274 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (339 : Vertex) [(274 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value74, value75, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (339 : Vertex) (337 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 75 = true := by
  rw [value75, value76, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(338 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (337 : Vertex) [(338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 74 = true := by
  rw [value74, value76, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(337 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (338 : Vertex) [(337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 60 = false ∨ valuation q 74 = false ∨ valuation q 80 = false := by
  rw [value60, value74, value77, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (277 : Vertex) (337 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 60 = false ∨ valuation q 74 = false ∨ valuation q 117 = false := by
  rw [value60, value74, value77, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (277 : Vertex) (337 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 60 = false ∨ valuation q 80 = false ∨ valuation q 117 = false := by
  rw [value60, value77, value80, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (277 : Vertex) (349 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 74 = false ∨ valuation q 80 = false ∨ valuation q 117 = false := by
  rw [value74, value77, value80, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (337 : Vertex) (349 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 201 = true ∨ valuation q 74 = true ∨ valuation q 80 = true ∨ valuation q 117 = true := by
  rw [value74, value77, value80, value117, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(337 : Vertex), (349 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (277 : Vertex) [(337 : Vertex), (349 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 78 = true := by
  rw [value78, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (345 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 71 = false ∨ valuation q 74 = false ∨ valuation q 80 = false := by
  rw [value71, value74, value78, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (329 : Vertex) (337 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 71 = false ∨ valuation q 74 = false := by
  rw [value71, value74, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (345 : Vertex) (329 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 71 = true ∨ valuation q 80 = true := by
  rw [value71, value78, value80, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(329 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (337 : Vertex) [(329 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E153.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112153
