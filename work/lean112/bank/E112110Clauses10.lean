import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value82, value83, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (395 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 202 = true ∨ valuation q 83 = true ∨ valuation q 93 = true ∨ valuation q 103 = true := by
  rw [value83, value84, value93, value103, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(394 : Vertex), (411 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (139 : Vertex) [(394 : Vertex), (411 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 202 = true ∨ valuation q 23 = true ∨ valuation q 93 = true ∨ valuation q 103 = true := by
  rw [value23, value84, value93, value103, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(139 : Vertex), (411 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (394 : Vertex) [(139 : Vertex), (411 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 202 = true ∨ valuation q 23 = true ∨ valuation q 83 = true ∨ valuation q 103 = true := by
  rw [value23, value83, value84, value103, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(139 : Vertex), (394 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (411 : Vertex) [(139 : Vertex), (394 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 202 = true ∨ valuation q 23 = true ∨ valuation q 83 = true ∨ valuation q 93 = true := by
  rw [value23, value83, value84, value93, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(139 : Vertex), (394 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (459 : Vertex) [(139 : Vertex), (394 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 86 = false := by
  rw [value79, value82, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 104 = false := by
  rw [value79, value82, value85, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (392 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 79 = false ∨ valuation q 86 = false ∨ valuation q 104 = false := by
  rw [value79, value85, value86, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 82 = false ∨ valuation q 86 = false ∨ valuation q 104 = false := by
  rw [value82, value85, value86, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (392 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 204 = true ∨ valuation q 83 = true ∨ valuation q 85 = true ∨ valuation q 106 = true := by
  rw [value83, value85, value86, value106, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(394 : Vertex), (396 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (390 : Vertex) [(394 : Vertex), (396 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 204 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 106 = true := by
  rw [value81, value85, value86, value106, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(390 : Vertex), (396 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (394 : Vertex) [(390 : Vertex), (396 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 204 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 106 = true := by
  rw [value81, value83, value86, value106, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(390 : Vertex), (394 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (396 : Vertex) [(390 : Vertex), (394 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 204 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 85 = true := by
  rw [value81, value83, value85, value86, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(390 : Vertex), (394 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (462 : Vertex) [(390 : Vertex), (394 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 78 = false ∨ valuation q 89 = false ∨ valuation q 110 = false := by
  rw [value78, value87, value89, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (406 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 205 = true ∨ valuation q 78 = true ∨ valuation q 110 = true := by
  rw [value78, value87, value110, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(386 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (406 : Vertex) [(386 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 80 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value80, value88, value90, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (389 : Vertex) (407 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 206 = true ∨ valuation q 90 = true ∨ valuation q 94 = true := by
  rw [value88, value90, value94, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(407 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (389 : Vertex) [(407 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 206 = true ∨ valuation q 80 = true ∨ valuation q 94 = true := by
  rw [value80, value88, value94, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(389 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (407 : Vertex) [(389 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 206 = true ∨ valuation q 80 = true ∨ valuation q 90 = true := by
  rw [value80, value88, value90, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(389 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (413 : Vertex) [(389 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 87 = true ∨ valuation q 90 = true := by
  rw [value87, value89, value90, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(402 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (390 : Vertex) [(402 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 81 = true ∨ valuation q 90 = true := by
  rw [value81, value89, value90, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(390 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (402 : Vertex) [(390 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 81 = true ∨ valuation q 87 = true := by
  rw [value81, value87, value89, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(390 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (407 : Vertex) [(390 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 95 = false := by
  rw [value88, value89, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (405 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 208 = true ∨ valuation q 88 = true ∨ valuation q 95 = true := by
  rw [value88, value90, value95, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(405 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (406 : Vertex) [(405 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 30 = false ∨ valuation q 82 = false ∨ valuation q 92 = false := by
  rw [value30, value82, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (152 : Vertex) (392 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 30 = false ∨ valuation q 82 = false ∨ valuation q 113 = false := by
  rw [value30, value82, value91, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (152 : Vertex) (392 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 30 = false ∨ valuation q 92 = false ∨ valuation q 113 = false := by
  rw [value30, value91, value92, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (152 : Vertex) (409 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 82 = false ∨ valuation q 92 = false ∨ valuation q 113 = false := by
  rw [value82, value91, value92, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (392 : Vertex) (409 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value91, value92, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (408 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 210 = true ∨ valuation q 93 = true ∨ valuation q 94 = true := by
  rw [value92, value93, value94, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(411 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (408 : Vertex) [(411 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 210 = true ∨ valuation q 91 = true ∨ valuation q 94 = true := by
  rw [value91, value92, value94, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(408 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (411 : Vertex) [(408 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 210 = true ∨ valuation q 91 = true ∨ valuation q 93 = true := by
  rw [value91, value92, value93, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(408 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (413 : Vertex) [(408 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E110.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112110
