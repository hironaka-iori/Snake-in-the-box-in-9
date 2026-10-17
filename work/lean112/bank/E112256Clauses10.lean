import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 174 = true ∨ valuation q 12 = true ∨ valuation q 39 = true ∨ valuation q 48 = true ∨ valuation q 52 = true := by
  rw [value12, value39, value47, value48, value52, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (212 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(84 : Vertex), (196 : Vertex), (213 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (212 : Vertex) (244 : Vertex) [(84 : Vertex), (196 : Vertex), (213 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 47 = false ∨ valuation q 49 = false ∨ valuation q 53 = false := by
  rw [value47, value48, value49, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (212 : Vertex) (215 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 47 = false ∨ valuation q 49 = false ∨ valuation q 67 = false := by
  rw [value47, value48, value49, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (212 : Vertex) (215 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 47 = false ∨ valuation q 49 = false ∨ valuation q 109 = false := by
  rw [value47, value48, value49, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (212 : Vertex) (215 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 47 = false ∨ valuation q 53 = false ∨ valuation q 67 = false := by
  rw [value47, value48, value53, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (212 : Vertex) (221 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 47 = false ∨ valuation q 53 = false ∨ valuation q 109 = false := by
  rw [value47, value48, value53, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (212 : Vertex) (221 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 53 = false ∨ valuation q 67 = false := by
  rw [value48, value49, value53, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (215 : Vertex) (221 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 53 = false ∨ valuation q 109 = false := by
  rw [value48, value49, value53, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (215 : Vertex) (221 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 67 = false ∨ valuation q 109 = false := by
  rw [value48, value49, value67, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (215 : Vertex) (245 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 67 = false ∨ valuation q 109 = false := by
  rw [value48, value53, value67, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (221 : Vertex) (245 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 49 = true := by
  rw [value49, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (215 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 13 = true ∨ valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 54 = true := by
  rw [value13, value46, value48, value49, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ∈ [(87 : Vertex), (211 : Vertex), (213 : Vertex), (223 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (215 : Vertex) [(87 : Vertex), (211 : Vertex), (213 : Vertex), (223 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 54 = false := by
  rw [value46, value48, value49, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (211 : Vertex) (213 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 176 = true ∨ valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 54 = true := by
  rw [value46, value48, value49, value54, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(211 : Vertex), (213 : Vertex), (223 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (87 : Vertex) [(211 : Vertex), (213 : Vertex), (223 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 176 = true ∨ valuation q 13 = true ∨ valuation q 48 = true ∨ valuation q 54 = true := by
  rw [value13, value48, value49, value54, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(87 : Vertex), (213 : Vertex), (223 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (211 : Vertex) [(87 : Vertex), (213 : Vertex), (223 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 176 = true ∨ valuation q 13 = true ∨ valuation q 46 = true ∨ valuation q 54 = true := by
  rw [value13, value46, value49, value54, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(87 : Vertex), (211 : Vertex), (223 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (213 : Vertex) [(87 : Vertex), (211 : Vertex), (223 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 176 = true ∨ valuation q 13 = true ∨ valuation q 46 = true ∨ valuation q 48 = true := by
  rw [value13, value46, value48, value49, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (223 : Vertex) → w ∈ [(87 : Vertex), (211 : Vertex), (213 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (223 : Vertex) [(87 : Vertex), (211 : Vertex), (213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 14 = false ∨ valuation q 41 = false ∨ valuation q 53 = false := by
  rw [value14, value41, value50, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (89 : Vertex) (201 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 14 = false ∨ valuation q 41 = false ∨ valuation q 111 = false := by
  rw [value14, value41, value50, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (89 : Vertex) (201 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 14 = false ∨ valuation q 53 = false ∨ valuation q 111 = false := by
  rw [value14, value50, value53, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (89 : Vertex) (221 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 41 = false ∨ valuation q 53 = false ∨ valuation q 111 = false := by
  rw [value41, value50, value53, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (201 : Vertex) (221 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 177 = true ∨ valuation q 41 = true ∨ valuation q 53 = true ∨ valuation q 111 = true := by
  rw [value41, value50, value53, value111, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(201 : Vertex), (221 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (89 : Vertex) [(201 : Vertex), (221 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 177 = true ∨ valuation q 14 = true ∨ valuation q 53 = true ∨ valuation q 111 = true := by
  rw [value14, value50, value53, value111, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(89 : Vertex), (221 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (201 : Vertex) [(89 : Vertex), (221 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 15 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value15, value42, value45, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (202 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 15 = false ∨ valuation q 42 = false ∨ valuation q 70 = false := by
  rw [value15, value42, value51, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (202 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 15 = false ∨ valuation q 45 = false ∨ valuation q 70 = false := by
  rw [value15, value45, value51, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (210 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 70 = false := by
  rw [value42, value45, value51, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (202 : Vertex) (210 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 178 = true ∨ valuation q 42 = true ∨ valuation q 45 = true ∨ valuation q 70 = true := by
  rw [value42, value45, value51, value70, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(202 : Vertex), (210 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (90 : Vertex) [(202 : Vertex), (210 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 178 = true ∨ valuation q 15 = true ∨ valuation q 42 = true ∨ valuation q 70 = true := by
  rw [value15, value42, value51, value70, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(90 : Vertex), (202 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (210 : Vertex) [(90 : Vertex), (202 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 43 = false ∨ valuation q 47 = false ∨ valuation q 53 = false := by
  rw [value43, value47, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (220 : Vertex) (204 : Vertex) (212 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 53 = false ∨ valuation q 113 = false := by
  rw [value47, value52, value53, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (220 : Vertex) (212 : Vertex) (221 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 16 = false ∨ valuation q 50 = false ∨ valuation q 54 = false := by
  rw [value16, value50, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (217 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E256.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112256
