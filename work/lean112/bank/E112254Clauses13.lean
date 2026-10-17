import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 73 = false ∨ valuation q 76 = false ∨ valuation q 80 = false := by
  rw [value73, value76, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (399 : Vertex) (407 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 203 = true ∨ valuation q 73 = true ∨ valuation q 76 = true ∨ valuation q 80 = true := by
  rw [value73, value76, value80, value81, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(399 : Vertex), (407 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (287 : Vertex) [(399 : Vertex), (407 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 203 = true ∨ valuation q 23 = true ∨ valuation q 76 = true ∨ valuation q 80 = true := by
  rw [value23, value76, value80, value81, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(287 : Vertex), (407 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (399 : Vertex) [(287 : Vertex), (407 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 203 = true ∨ valuation q 23 = true ∨ valuation q 73 = true ∨ valuation q 80 = true := by
  rw [value23, value73, value80, value81, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(287 : Vertex), (399 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (407 : Vertex) [(287 : Vertex), (399 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 203 = true ∨ valuation q 23 = true ∨ valuation q 73 = true ∨ valuation q 76 = true := by
  rw [value23, value73, value76, value81, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(287 : Vertex), (399 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (413 : Vertex) [(287 : Vertex), (399 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 24 = false ∨ valuation q 84 = false ∨ valuation q 91 = false := by
  rw [value24, value82, value84, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (420 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 204 = true ∨ valuation q 64 = true ∨ valuation q 84 = true ∨ valuation q 91 = true := by
  rw [value64, value82, value84, value91, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(384 : Vertex), (420 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (288 : Vertex) [(384 : Vertex), (420 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 204 = true ∨ valuation q 24 = true ∨ valuation q 84 = true ∨ valuation q 91 = true := by
  rw [value24, value82, value84, value91, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(288 : Vertex), (420 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (384 : Vertex) [(288 : Vertex), (420 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 204 = true ∨ valuation q 24 = true ∨ valuation q 64 = true ∨ valuation q 91 = true := by
  rw [value24, value64, value82, value91, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(288 : Vertex), (384 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (420 : Vertex) [(288 : Vertex), (384 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 93 = false := by
  rw [value83, value85, value88, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (423 : Vertex) (427 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 205 = true ∨ valuation q 88 = true ∨ valuation q 93 = true := by
  rw [value83, value88, value93, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (423 : Vertex) [(427 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 205 = true ∨ valuation q 85 = true ∨ valuation q 93 = true := by
  rw [value83, value85, value93, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(423 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (427 : Vertex) [(423 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 205 = true ∨ valuation q 85 = true ∨ valuation q 88 = true := by
  rw [value83, value85, value88, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(423 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (435 : Vertex) [(423 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 67 = false ∨ valuation q 82 = false ∨ valuation q 94 = false := by
  rw [value67, value82, value84, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (388 : Vertex) (416 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 206 = true ∨ valuation q 82 = true ∨ valuation q 94 = true := by
  rw [value82, value84, value94, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (388 : Vertex) → w ∈ [(416 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (388 : Vertex) [(416 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 206 = true ∨ valuation q 67 = true ∨ valuation q 94 = true := by
  rw [value67, value84, value94, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (416 : Vertex) → w ∈ [(388 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (416 : Vertex) [(388 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 27 = false ∨ valuation q 69 = false ∨ valuation q 83 = false := by
  rw [value27, value69, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (391 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 27 = false ∨ valuation q 83 = false := by
  rw [value27, value83, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (423 : Vertex) (295 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 207 = true ∨ valuation q 69 = true ∨ valuation q 83 = true := by
  rw [value69, value83, value85, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (423 : Vertex) w → w ∈ region → w ≠ (295 : Vertex) → w ∈ [(391 : Vertex), (419 : Vertex)] := by decide
  have hg := other_cover q (423 : Vertex) (295 : Vertex) [(391 : Vertex), (419 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 207 = true ∨ valuation q 27 = true ∨ valuation q 83 = true := by
  rw [value27, value83, value85, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (423 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(295 : Vertex), (419 : Vertex)] := by decide
  have hg := other_cover q (423 : Vertex) (391 : Vertex) [(295 : Vertex), (419 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 207 = true ∨ valuation q 27 = true ∨ valuation q 69 = true := by
  rw [value27, value69, value85, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (423 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(295 : Vertex), (391 : Vertex)] := by decide
  have hg := other_cover q (423 : Vertex) (419 : Vertex) [(295 : Vertex), (391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 28 = false ∨ valuation q 71 = false ∨ valuation q 115 = false := by
  rw [value28, value71, value86, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (297 : Vertex) (393 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 28 = false ∨ valuation q 89 = false ∨ valuation q 115 = false := by
  rw [value28, value86, value89, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (297 : Vertex) (429 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 71 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value71, value86, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (393 : Vertex) (427 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 71 = false ∨ valuation q 88 = false ∨ valuation q 115 = false := by
  rw [value71, value86, value88, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (393 : Vertex) (427 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 208 = true ∨ valuation q 28 = true ∨ valuation q 71 = true ∨ valuation q 88 = true ∨ valuation q 89 = true := by
  rw [value28, value71, value86, value88, value89, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(297 : Vertex), (393 : Vertex), (427 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (489 : Vertex) [(297 : Vertex), (393 : Vertex), (427 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value87, value88, value90, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (427 : Vertex) (430 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 209 = true ∨ valuation q 90 = true ∨ valuation q 98 = true := by
  rw [value87, value90, value98, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(430 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (427 : Vertex) [(430 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 209 = true ∨ valuation q 88 = true ∨ valuation q 98 = true := by
  rw [value87, value88, value98, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(427 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (430 : Vertex) [(427 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 209 = true ∨ valuation q 88 = true ∨ valuation q 90 = true := by
  rw [value87, value88, value90, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(427 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (442 : Vertex) [(427 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 29 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value29, value83, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (419 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 29 = false ∨ valuation q 83 = false ∨ valuation q 87 = false := by
  rw [value29, value83, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (419 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E254.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112254
