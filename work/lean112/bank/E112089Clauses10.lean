import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 172 = true ∨ valuation q 46 = true ∨ valuation q 47 = true := by
  rw [value46, value47, value48, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(145 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (151 : Vertex) [(145 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 39 = false ∨ valuation q 47 = false := by
  rw [value14, value39, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (134 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 39 = false ∨ valuation q 50 = false := by
  rw [value14, value39, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (134 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 39 = false ∨ valuation q 73 = false := by
  rw [value14, value39, value49, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (134 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 39 = false ∨ valuation q 103 = false := by
  rw [value14, value39, value49, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (134 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value14, value47, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (148 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 47 = false ∨ valuation q 73 = false := by
  rw [value14, value47, value49, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (148 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 47 = false ∨ valuation q 103 = false := by
  rw [value14, value47, value49, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (148 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 50 = false ∨ valuation q 73 = false := by
  rw [value14, value49, value50, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (151 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 50 = false ∨ valuation q 103 = false := by
  rw [value14, value49, value50, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (151 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 73 = false ∨ valuation q 103 = false := by
  rw [value14, value49, value73, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (214 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 39 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value39, value47, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (134 : Vertex) (148 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 39 = false ∨ valuation q 47 = false ∨ valuation q 73 = false := by
  rw [value39, value47, value49, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (134 : Vertex) (148 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 39 = false ∨ valuation q 47 = false ∨ valuation q 103 = false := by
  rw [value39, value47, value49, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (134 : Vertex) (148 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 39 = false ∨ valuation q 50 = false ∨ valuation q 73 = false := by
  rw [value39, value49, value50, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (134 : Vertex) (151 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 39 = false ∨ valuation q 50 = false ∨ valuation q 103 = false := by
  rw [value39, value49, value50, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (134 : Vertex) (151 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 39 = false ∨ valuation q 73 = false ∨ valuation q 103 = false := by
  rw [value39, value49, value73, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (134 : Vertex) (214 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 73 = false := by
  rw [value47, value49, value50, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (148 : Vertex) (151 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 103 = false := by
  rw [value47, value49, value50, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (148 : Vertex) (151 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 47 = false ∨ valuation q 73 = false ∨ valuation q 103 = false := by
  rw [value47, value49, value73, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (148 : Vertex) (214 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 73 = false ∨ valuation q 103 = false := by
  rw [value49, value50, value73, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (151 : Vertex) (214 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 173 = true ∨ valuation q 14 = true ∨ valuation q 47 = true ∨ valuation q 50 = true ∨ valuation q 73 = true ∨ valuation q 103 = true := by
  rw [value14, value47, value49, value50, value73, value103, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(22 : Vertex), (148 : Vertex), (151 : Vertex), (214 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (134 : Vertex) [(22 : Vertex), (148 : Vertex), (151 : Vertex), (214 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 173 = true ∨ valuation q 14 = true ∨ valuation q 39 = true ∨ valuation q 50 = true ∨ valuation q 73 = true ∨ valuation q 103 = true := by
  rw [value14, value39, value49, value50, value73, value103, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(22 : Vertex), (134 : Vertex), (151 : Vertex), (214 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (148 : Vertex) [(22 : Vertex), (134 : Vertex), (151 : Vertex), (214 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 173 = true ∨ valuation q 14 = true ∨ valuation q 39 = true ∨ valuation q 47 = true ∨ valuation q 73 = true ∨ valuation q 103 = true := by
  rw [value14, value39, value47, value49, value73, value103, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(22 : Vertex), (134 : Vertex), (148 : Vertex), (214 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (151 : Vertex) [(22 : Vertex), (134 : Vertex), (148 : Vertex), (214 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 50 = true := by
  rw [value50, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (151 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 55 = true := by
  rw [value48, value49, value50, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ∈ [(149 : Vertex), (150 : Vertex), (159 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (151 : Vertex) [(149 : Vertex), (150 : Vertex), (159 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 55 = false := by
  rw [value48, value49, value50, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (149 : Vertex) (150 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value48, value49, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (151 : Vertex) (149 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 49 = false ∨ valuation q 55 = false := by
  rw [value49, value55, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (151 : Vertex) (150 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 174 = true ∨ valuation q 49 = true ∨ valuation q 55 = true := by
  rw [value49, value50, value55, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(150 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (149 : Vertex) [(150 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 174 = true ∨ valuation q 48 = true ∨ valuation q 55 = true := by
  rw [value48, value50, value55, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(149 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (150 : Vertex) [(149 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 174 = true ∨ valuation q 48 = true ∨ valuation q 49 = true := by
  rw [value48, value49, value50, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(149 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (159 : Vertex) [(149 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E089.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112089
