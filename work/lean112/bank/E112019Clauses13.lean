import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 203 = true ∨ valuation q 79 = true ∨ valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 88 = true := by
  rw [value79, value82, value83, value84, value88, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(384 : Vertex), (389 : Vertex), (390 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (132 : Vertex) [(384 : Vertex), (389 : Vertex), (390 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 203 = true ∨ valuation q 25 = true ∨ valuation q 79 = true ∨ valuation q 84 = true ∨ valuation q 88 = true := by
  rw [value25, value79, value82, value84, value88, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(132 : Vertex), (384 : Vertex), (390 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (389 : Vertex) [(132 : Vertex), (384 : Vertex), (390 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 203 = true ∨ valuation q 25 = true ∨ valuation q 79 = true ∨ valuation q 83 = true ∨ valuation q 88 = true := by
  rw [value25, value79, value82, value83, value88, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(132 : Vertex), (384 : Vertex), (389 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (390 : Vertex) [(132 : Vertex), (384 : Vertex), (389 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 203 = true ∨ valuation q 25 = true ∨ valuation q 79 = true ∨ valuation q 83 = true ∨ valuation q 84 = true := by
  rw [value25, value79, value82, value83, value84, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(132 : Vertex), (384 : Vertex), (389 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (396 : Vertex) [(132 : Vertex), (384 : Vertex), (389 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 26 = false ∨ valuation q 80 = false ∨ valuation q 82 = false := by
  rw [value26, value80, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (385 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 26 = false ∨ valuation q 80 = false ∨ valuation q 91 = false := by
  rw [value26, value80, value83, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (385 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 26 = false ∨ valuation q 80 = false ∨ valuation q 103 = false := by
  rw [value26, value80, value83, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (385 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 26 = false ∨ valuation q 82 = false ∨ valuation q 91 = false := by
  rw [value26, value82, value83, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (388 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 26 = false ∨ valuation q 82 = false ∨ valuation q 103 = false := by
  rw [value26, value82, value83, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (388 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 26 = false ∨ valuation q 91 = false ∨ valuation q 103 = false := by
  rw [value26, value83, value91, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (405 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 91 = false := by
  rw [value80, value82, value83, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (388 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 103 = false := by
  rw [value80, value82, value83, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (388 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 91 = false ∨ valuation q 103 = false := by
  rw [value80, value83, value91, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (405 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 91 = false ∨ valuation q 103 = false := by
  rw [value82, value83, value91, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (388 : Vertex) (405 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 89 = false := by
  rw [value81, value82, value84, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 92 = false := by
  rw [value81, value82, value84, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 89 = false ∨ valuation q 92 = false := by
  rw [value81, value84, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (398 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 89 = false ∨ valuation q 92 = false := by
  rw [value82, value84, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (388 : Vertex) (398 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 205 = true ∨ valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 89 = true := by
  rw [value81, value82, value84, value89, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(386 : Vertex), (388 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (406 : Vertex) [(386 : Vertex), (388 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 85 = true := by
  rw [value85, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (392 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 79 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 94 = true ∨ valuation q 105 = true := by
  rw [value79, value85, value86, value88, value94, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ∈ [(384 : Vertex), (394 : Vertex), (396 : Vertex), (408 : Vertex), (456 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (392 : Vertex) [(384 : Vertex), (394 : Vertex), (396 : Vertex), (408 : Vertex), (456 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 79 = false ∨ valuation q 88 = false ∨ valuation q 94 = false := by
  rw [value79, value85, value88, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (384 : Vertex) (396 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 94 = false ∨ valuation q 105 = false := by
  rw [value85, value86, value94, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (394 : Vertex) (408 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 206 = true ∨ valuation q 79 = true ∨ valuation q 88 = true ∨ valuation q 94 = true ∨ valuation q 105 = true := by
  rw [value79, value85, value88, value94, value105, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(384 : Vertex), (396 : Vertex), (408 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (394 : Vertex) [(384 : Vertex), (396 : Vertex), (408 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 206 = true ∨ valuation q 79 = true ∨ valuation q 86 = true ∨ valuation q 94 = true ∨ valuation q 105 = true := by
  rw [value79, value85, value86, value94, value105, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(384 : Vertex), (394 : Vertex), (408 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (396 : Vertex) [(384 : Vertex), (394 : Vertex), (408 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 206 = true ∨ valuation q 79 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 105 = true := by
  rw [value79, value85, value86, value88, value105, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(384 : Vertex), (394 : Vertex), (396 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (408 : Vertex) [(384 : Vertex), (394 : Vertex), (396 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 206 = true ∨ valuation q 79 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 94 = true := by
  rw [value79, value85, value86, value88, value94, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(384 : Vertex), (394 : Vertex), (396 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (456 : Vertex) [(384 : Vertex), (394 : Vertex), (396 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 28 = false ∨ valuation q 58 = false ∨ valuation q 81 = false := by
  rw [value28, value58, value81, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (266 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 28 = false ∨ valuation q 58 = false ∨ valuation q 85 = false := by
  rw [value28, value58, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (266 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 28 = false ∨ valuation q 58 = false ∨ valuation q 87 = false := by
  rw [value28, value58, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (266 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 28 = false ∨ valuation q 58 = false ∨ valuation q 89 = false := by
  rw [value28, value58, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (266 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 28 = false ∨ valuation q 81 = false ∨ valuation q 85 = false := by
  rw [value28, value81, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (386 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E019.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112019
