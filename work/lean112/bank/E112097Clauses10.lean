import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 201 = true ∨ valuation q 70 = true ∨ valuation q 79 = true := by
  rw [value70, value78, value79, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(360 : Vertex), (380 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (368 : Vertex) [(360 : Vertex), (380 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 201 = true ∨ valuation q 70 = true ∨ valuation q 74 = true := by
  rw [value70, value74, value78, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (380 : Vertex) → w ∈ [(360 : Vertex), (368 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (380 : Vertex) [(360 : Vertex), (368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 202 = true ∨ valuation q 78 = true ∨ valuation q 80 = true := by
  rw [value78, value79, value80, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (380 : Vertex) w → w ∈ region → w ≠ (372 : Vertex) → w ∈ [(376 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (380 : Vertex) (372 : Vertex) [(376 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 202 = true ∨ valuation q 77 = true ∨ valuation q 80 = true := by
  rw [value77, value79, value80, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (380 : Vertex) w → w ∈ region → w ≠ (376 : Vertex) → w ∈ [(372 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (380 : Vertex) (376 : Vertex) [(372 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 202 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value77, value78, value79, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (380 : Vertex) w → w ∈ region → w ≠ (381 : Vertex) → w ∈ [(372 : Vertex), (376 : Vertex)] := by decide
  have hg := other_cover q (380 : Vertex) (381 : Vertex) [(372 : Vertex), (376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 122 = false := by
  rw [value79, value80, value81, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (380 : Vertex) (383 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 203 = true ∨ valuation q 81 = true ∨ valuation q 122 = true := by
  rw [value80, value81, value122, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (380 : Vertex) → w ∈ [(383 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (380 : Vertex) [(383 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 203 = true ∨ valuation q 79 = true ∨ valuation q 122 = true := by
  rw [value79, value80, value122, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(380 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (383 : Vertex) [(380 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 73 = false ∨ valuation q 80 = false ∨ valuation q 123 = false := by
  rw [value73, value80, value81, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (367 : Vertex) (381 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 204 = true ∨ valuation q 80 = true ∨ valuation q 123 = true := by
  rw [value80, value81, value123, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(381 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (383 : Vertex) (367 : Vertex) [(381 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 204 = true ∨ valuation q 73 = true ∨ valuation q 123 = true := by
  rw [value73, value81, value123, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ≠ (381 : Vertex) → w ∈ [(367 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (383 : Vertex) (381 : Vertex) [(367 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 204 = true ∨ valuation q 73 = true ∨ valuation q 80 = true := by
  rw [value73, value80, value81, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ≠ (511 : Vertex) → w ∈ [(367 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (383 : Vertex) (511 : Vertex) [(367 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 92 = false ∨ valuation q 102 = false := by
  rw [value82, value83, value92, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (419 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 205 = true ∨ valuation q 84 = true ∨ valuation q 92 = true ∨ valuation q 102 = true := by
  rw [value82, value84, value92, value102, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(421 : Vertex), (433 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (419 : Vertex) [(421 : Vertex), (433 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 205 = true ∨ valuation q 83 = true ∨ valuation q 92 = true ∨ valuation q 102 = true := by
  rw [value82, value83, value92, value102, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(419 : Vertex), (433 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (421 : Vertex) [(419 : Vertex), (433 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 205 = true ∨ valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 102 = true := by
  rw [value82, value83, value84, value102, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(419 : Vertex), (421 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (433 : Vertex) [(419 : Vertex), (421 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 205 = true ∨ valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 92 = true := by
  rw [value82, value83, value84, value92, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(419 : Vertex), (421 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (481 : Vertex) [(419 : Vertex), (421 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 87 = false ∨ valuation q 94 = false := by
  rw [value82, value83, value87, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (417 : Vertex) (427 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 206 = true ∨ valuation q 87 = true ∨ valuation q 94 = true := by
  rw [value83, value87, value94, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (417 : Vertex) [(427 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 206 = true ∨ valuation q 82 = true ∨ valuation q 94 = true := by
  rw [value82, value83, value94, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(417 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (427 : Vertex) [(417 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 206 = true ∨ valuation q 82 = true ∨ valuation q 87 = true := by
  rw [value82, value83, value87, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(417 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (435 : Vertex) [(417 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 82 = false ∨ valuation q 105 = false := by
  rw [value82, value105, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (421 : Vertex) (417 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 207 = true ∨ valuation q 105 = true := by
  rw [value84, value105, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(485 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (417 : Vertex) [(485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 89 = false ∨ valuation q 95 = false ∨ valuation q 106 = false := by
  rw [value85, value89, value95, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (430 : Vertex) (438 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 96 = false := by
  rw [value17, value52, value86, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 52 = false ∨ valuation q 88 = false ∨ valuation q 96 = false := by
  rw [value52, value86, value88, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 52 = false ∨ valuation q 88 = false ∨ valuation q 107 = false := by
  rw [value52, value86, value88, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (428 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 52 = false ∨ valuation q 96 = false ∨ valuation q 107 = false := by
  rw [value52, value86, value96, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 96 = false ∨ valuation q 107 = false := by
  rw [value86, value88, value96, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (428 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 209 = true ∨ valuation q 52 = true ∨ valuation q 88 = true ∨ valuation q 96 = true ∨ valuation q 107 = true := by
  rw [value52, value86, value88, value96, value107, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(296 : Vertex), (428 : Vertex), (440 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (168 : Vertex) [(296 : Vertex), (428 : Vertex), (440 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 209 = true ∨ valuation q 17 = true ∨ valuation q 88 = true ∨ valuation q 96 = true ∨ valuation q 107 = true := by
  rw [value17, value86, value88, value96, value107, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(168 : Vertex), (428 : Vertex), (440 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (296 : Vertex) [(168 : Vertex), (428 : Vertex), (440 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 209 = true ∨ valuation q 17 = true ∨ valuation q 52 = true ∨ valuation q 96 = true ∨ valuation q 107 = true := by
  rw [value17, value52, value86, value96, value107, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(168 : Vertex), (296 : Vertex), (440 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (428 : Vertex) [(168 : Vertex), (296 : Vertex), (440 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E097.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112097
