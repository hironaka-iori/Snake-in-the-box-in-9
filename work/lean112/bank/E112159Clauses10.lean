import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 208 = true ∨ valuation q 20 = true ∨ valuation q 86 = true ∨ valuation q 91 = true := by
  rw [value20, value86, value90, value91, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(174 : Vertex), (422 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (302 : Vertex) [(174 : Vertex), (422 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 21 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value21, value87, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 24 = false ∨ valuation q 95 = false ∨ valuation q 99 = false := by
  rw [value24, value92, value95, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (178 : Vertex) (438 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 210 = true ∨ valuation q 24 = true ∨ valuation q 95 = true := by
  rw [value24, value92, value95, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(178 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (442 : Vertex) [(178 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 26 = true ∨ valuation q 96 = true ∨ valuation q 100 = true := by
  rw [value26, value94, value96, value100, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(181 : Vertex), (439 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (436 : Vertex) [(181 : Vertex), (439 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 26 = true ∨ valuation q 93 = true ∨ valuation q 100 = true := by
  rw [value26, value93, value94, value100, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(181 : Vertex), (436 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (439 : Vertex) [(181 : Vertex), (436 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 87 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value87, value94, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (439 : Vertex) (423 : Vertex) (437 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 87 = false ∨ valuation q 94 = false ∨ valuation q 113 = false := by
  rw [value87, value94, value96, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (439 : Vertex) (423 : Vertex) (437 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 87 = false ∨ valuation q 95 = false ∨ valuation q 113 = false := by
  rw [value87, value95, value96, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (439 : Vertex) (423 : Vertex) (438 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 113 = false := by
  rw [value94, value95, value96, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (439 : Vertex) (437 : Vertex) (438 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 88 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value88, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (424 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value97, value98, value99, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (424 : Vertex) [(441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 88 = true ∨ valuation q 98 = true := by
  rw [value88, value97, value98, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(424 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (442 : Vertex) [(424 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 89 = false ∨ valuation q 97 = false ∨ valuation q 114 = false := by
  rw [value89, value97, value98, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (425 : Vertex) (440 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 89 = false ∨ valuation q 100 = false ∨ valuation q 114 = false := by
  rw [value89, value98, value100, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (425 : Vertex) (445 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 97 = false ∨ valuation q 100 = false ∨ valuation q 114 = false := by
  rw [value97, value98, value100, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (440 : Vertex) (445 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 216 = true ∨ valuation q 97 = true ∨ valuation q 100 = true ∨ valuation q 114 = true := by
  rw [value97, value98, value100, value114, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(440 : Vertex), (445 : Vertex), (505 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (425 : Vertex) [(440 : Vertex), (445 : Vertex), (505 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 216 = true ∨ valuation q 89 = true ∨ valuation q 100 = true ∨ valuation q 114 = true := by
  rw [value89, value98, value100, value114, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(425 : Vertex), (445 : Vertex), (505 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (440 : Vertex) [(425 : Vertex), (445 : Vertex), (505 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 97 = true := by
  rw [value97, value99, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (442 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(440 : Vertex)] := by decide
  have hg := other_cover q (442 : Vertex) (434 : Vertex) [(440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 92 = true := by
  rw [value92, value99, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (442 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(434 : Vertex)] := by decide
  have hg := other_cover q (442 : Vertex) (440 : Vertex) [(434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 29 = false ∨ valuation q 66 = false ∨ valuation q 94 = false := by
  rw [value29, value66, value94, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (445 : Vertex) (189 : Vertex) (317 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 29 = false ∨ valuation q 66 = false ∨ valuation q 98 = false := by
  rw [value29, value66, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (445 : Vertex) (189 : Vertex) (317 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 29 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value29, value94, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (445 : Vertex) (189 : Vertex) (437 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 66 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value66, value94, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (445 : Vertex) (317 : Vertex) (437 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 219 = true ∨ valuation q 103 = true ∨ valuation q 110 = true := by
  rw [value101, value103, value110, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [(484 : Vertex), (496 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (482 : Vertex) [(484 : Vertex), (496 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 219 = true ∨ valuation q 102 = true ∨ valuation q 110 = true := by
  rw [value101, value102, value110, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (484 : Vertex) → w ∈ [(482 : Vertex), (496 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (484 : Vertex) [(482 : Vertex), (496 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 101 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value101, value102, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (480 : Vertex) (486 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 220 = true ∨ valuation q 105 = true ∨ valuation q 106 = true := by
  rw [value102, value105, value106, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(486 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (480 : Vertex) [(486 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 101 = false ∨ valuation q 104 = false ∨ valuation q 108 = false := by
  rw [value101, value103, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (484 : Vertex) (480 : Vertex) (485 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 101 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value101, value103, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (484 : Vertex) (480 : Vertex) (486 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value103, value104, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (484 : Vertex) (485 : Vertex) (486 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 222 = true ∨ valuation q 103 = true ∨ valuation q 109 = true := by
  rw [value103, value104, value109, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (485 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(484 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (485 : Vertex) (229 : Vertex) [(484 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E159.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112159
