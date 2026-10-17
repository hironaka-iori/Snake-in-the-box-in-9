import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 23 = false ∨ valuation q 56 = false ∨ valuation q 82 = false := by
  rw [value23, value25, value56, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (52 : Vertex) (182 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 30 = false ∨ valuation q 56 = false := by
  rw [value25, value26, value30, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (55 : Vertex) (62 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 30 = false ∨ valuation q 82 = false := by
  rw [value25, value26, value30, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (55 : Vertex) (62 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 30 = false ∨ valuation q 56 = false ∨ valuation q 82 = false := by
  rw [value25, value30, value56, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (62 : Vertex) (182 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 24 = false := by
  rw [value14, value22, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (39 : Vertex) (51 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value14, value22, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (39 : Vertex) (51 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 31 = false := by
  rw [value14, value22, value26, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (39 : Vertex) (51 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 14 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value14, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (39 : Vertex) (53 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 14 = false ∨ valuation q 24 = false ∨ valuation q 31 = false := by
  rw [value14, value24, value26, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (39 : Vertex) (53 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 14 = false ∨ valuation q 25 = false ∨ valuation q 31 = false := by
  rw [value14, value25, value26, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (39 : Vertex) (54 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value22, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (51 : Vertex) (53 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 31 = false := by
  rw [value22, value24, value26, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (51 : Vertex) (53 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 31 = false := by
  rw [value22, value25, value26, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (51 : Vertex) (54 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 31 = false := by
  rw [value24, value25, value26, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (53 : Vertex) (54 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 152 = true ∨ valuation q 22 = true ∨ valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 31 = true := by
  rw [value22, value24, value25, value26, value31, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (39 : Vertex) → w ∈ [(51 : Vertex), (53 : Vertex), (54 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (39 : Vertex) [(51 : Vertex), (53 : Vertex), (54 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 152 = true ∨ valuation q 14 = true ∨ valuation q 22 = true ∨ valuation q 25 = true ∨ valuation q 31 = true := by
  rw [value14, value22, value25, value26, value31, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(39 : Vertex), (51 : Vertex), (54 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (53 : Vertex) [(39 : Vertex), (51 : Vertex), (54 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 153 = true ∨ valuation q 20 = true ∨ valuation q 29 = true := by
  rw [value20, value27, value29, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(49 : Vertex), (59 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (41 : Vertex) [(49 : Vertex), (59 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 153 = true ∨ valuation q 16 = true ∨ valuation q 29 = true := by
  rw [value16, value27, value29, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(41 : Vertex), (59 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (49 : Vertex) [(41 : Vertex), (59 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 153 = true ∨ valuation q 16 = true ∨ valuation q 20 = true := by
  rw [value16, value20, value27, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (59 : Vertex) → w ∈ [(41 : Vertex), (49 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (59 : Vertex) [(41 : Vertex), (49 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 29 = false := by
  rw [value17, value21, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (50 : Vertex) (59 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 17 = false ∨ valuation q 29 = false ∨ valuation q 40 = false := by
  rw [value17, value28, value29, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (59 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 17 = false ∨ valuation q 29 = false ∨ valuation q 83 = false := by
  rw [value17, value28, value29, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (59 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 154 = true ∨ valuation q 21 = true ∨ valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 40 = true ∨ valuation q 83 = true := by
  rw [value21, value28, value29, value30, value40, value83, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (58 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(50 : Vertex), (59 : Vertex), (62 : Vertex), (122 : Vertex), (314 : Vertex)] := by decide
  have hg := other_cover q (58 : Vertex) (42 : Vertex) [(50 : Vertex), (59 : Vertex), (62 : Vertex), (122 : Vertex), (314 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 154 = true ∨ valuation q 17 = true ∨ valuation q 21 = true ∨ valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 40 = true := by
  rw [value17, value21, value28, value29, value30, value40, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (58 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(42 : Vertex), (50 : Vertex), (59 : Vertex), (62 : Vertex), (122 : Vertex)] := by decide
  have hg := other_cover q (58 : Vertex) (314 : Vertex) [(42 : Vertex), (50 : Vertex), (59 : Vertex), (62 : Vertex), (122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 22 = false ∨ valuation q 27 = false ∨ valuation q 28 = false := by
  rw [value22, value27, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (59 : Vertex) (51 : Vertex) (57 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 22 = false ∨ valuation q 27 = false ∨ valuation q 31 = false := by
  rw [value22, value27, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (59 : Vertex) (51 : Vertex) (57 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 22 = false ∨ valuation q 28 = false ∨ valuation q 31 = false := by
  rw [value22, value28, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (59 : Vertex) (51 : Vertex) (58 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 31 = false := by
  rw [value27, value28, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (59 : Vertex) (57 : Vertex) (58 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 155 = true ∨ valuation q 22 = true ∨ valuation q 27 = true ∨ valuation q 31 = true := by
  rw [value22, value27, value29, value31, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(51 : Vertex), (57 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (58 : Vertex) [(51 : Vertex), (57 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 155 = true ∨ valuation q 22 = true ∨ valuation q 27 = true ∨ valuation q 28 = true := by
  rw [value22, value27, value28, value29, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (63 : Vertex) → w ∈ [(51 : Vertex), (57 : Vertex), (58 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (63 : Vertex) [(51 : Vertex), (57 : Vertex), (58 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 28 = false := by
  rw [value19, value25, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (54 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 31 = false := by
  rw [value19, value25, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (54 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E121.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112121
