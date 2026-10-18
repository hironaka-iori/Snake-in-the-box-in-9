import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 170 = true ∨ valuation q 52 = true ∨ valuation q 113 = true := by
  rw [value49, value52, value113, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(214 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (218 : Vertex) [(214 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 18 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value18, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (213 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 18 = false ∨ valuation q 51 = false ∨ valuation q 115 = false := by
  rw [value18, value50, value51, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (213 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 18 = false ∨ valuation q 52 = false ∨ valuation q 115 = false := by
  rw [value18, value50, value52, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (214 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 35 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value35, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (148 : Vertex) (213 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 35 = false ∨ valuation q 51 = false ∨ valuation q 115 = false := by
  rw [value35, value50, value51, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (148 : Vertex) (213 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 35 = false ∨ valuation q 52 = false ∨ valuation q 115 = false := by
  rw [value35, value50, value52, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (148 : Vertex) (214 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 115 = false := by
  rw [value50, value51, value52, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (213 : Vertex) (214 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 171 = true ∨ valuation q 18 = true ∨ valuation q 35 = true ∨ valuation q 52 = true ∨ valuation q 115 = true := by
  rw [value18, value35, value50, value52, value115, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (212 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(84 : Vertex), (148 : Vertex), (214 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (212 : Vertex) (213 : Vertex) [(84 : Vertex), (148 : Vertex), (214 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 51 = true := by
  rw [value51, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (213 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = true ∨ valuation q 53 = true ∨ valuation q 57 = true := by
  rw [value50, value51, value53, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ∈ [(212 : Vertex), (215 : Vertex), (221 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (213 : Vertex) [(212 : Vertex), (215 : Vertex), (221 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 50 = false ∨ valuation q 57 = false := by
  rw [value50, value57, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (213 : Vertex) (212 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 172 = true ∨ valuation q 53 = true ∨ valuation q 57 = true := by
  rw [value51, value53, value57, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(215 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (212 : Vertex) [(215 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 172 = true ∨ valuation q 50 = true ∨ valuation q 57 = true := by
  rw [value50, value51, value57, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(212 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (215 : Vertex) [(212 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 172 = true ∨ valuation q 50 = true ∨ valuation q 53 = true := by
  rw [value50, value51, value53, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(212 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (221 : Vertex) [(212 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 42 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value42, value49, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (214 : Vertex) (198 : Vertex) (210 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 42 = false ∨ valuation q 49 = false ∨ valuation q 53 = false := by
  rw [value42, value49, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (214 : Vertex) (198 : Vertex) (210 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 173 = true ∨ valuation q 49 = true ∨ valuation q 50 = true ∨ valuation q 53 = true := by
  rw [value49, value50, value52, value53, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(210 : Vertex), (212 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (198 : Vertex) [(210 : Vertex), (212 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 173 = true ∨ valuation q 42 = true ∨ valuation q 50 = true ∨ valuation q 53 = true := by
  rw [value42, value50, value52, value53, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(198 : Vertex), (212 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (210 : Vertex) [(198 : Vertex), (212 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 173 = true ∨ valuation q 42 = true ∨ valuation q 49 = true ∨ valuation q 53 = true := by
  rw [value42, value49, value52, value53, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(198 : Vertex), (210 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (212 : Vertex) [(198 : Vertex), (210 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 173 = true ∨ valuation q 42 = true ∨ valuation q 49 = true ∨ valuation q 50 = true := by
  rw [value42, value49, value50, value52, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(198 : Vertex), (210 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (215 : Vertex) [(198 : Vertex), (210 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 43 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value43, value51, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (199 : Vertex) (213 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 174 = true ∨ valuation q 51 = true ∨ valuation q 52 = true := by
  rw [value51, value52, value53, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(213 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (199 : Vertex) [(213 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 174 = true ∨ valuation q 43 = true ∨ valuation q 52 = true := by
  rw [value43, value52, value53, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(199 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (213 : Vertex) [(199 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 54 = true := by
  rw [value54, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (217 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 45 = true ∨ valuation q 56 = true ∨ valuation q 57 = true := by
  rw [value45, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ∈ [(201 : Vertex), (219 : Vertex), (221 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (217 : Vertex) [(201 : Vertex), (219 : Vertex), (221 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 45 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value45, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (201 : Vertex) (219 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value56, value57, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (217 : Vertex) (219 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 175 = true ∨ valuation q 56 = true ∨ valuation q 57 = true := by
  rw [value54, value56, value57, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(219 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (201 : Vertex) [(219 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 175 = true ∨ valuation q 45 = true ∨ valuation q 57 = true := by
  rw [value45, value54, value57, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(201 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (219 : Vertex) [(201 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 175 = true ∨ valuation q 45 = true ∨ valuation q 56 = true := by
  rw [value45, value54, value56, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(201 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (221 : Vertex) [(201 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 55 = true := by
  rw [value55, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (218 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem block7 (q : Snake 81) (h : Conditions q) : B112E019.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112019
