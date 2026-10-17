import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 54 = false ∨ valuation q 102 = false ∨ valuation q 114 = false := by
  rw [value54, value90, value102, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 102 = false := by
  rw [value90, value91, value92, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (397 : Vertex) (398 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 114 = false := by
  rw [value90, value91, value92, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (397 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 102 = false ∨ valuation q 114 = false := by
  rw [value90, value91, value102, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (397 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 92 = false ∨ valuation q 102 = false ∨ valuation q 114 = false := by
  rw [value90, value92, value102, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (398 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value86, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (389 : Vertex) (393 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 103 = false := by
  rw [value86, value88, value91, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (389 : Vertex) (393 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 93 = false := by
  rw [value88, value90, value91, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (393 : Vertex) (396 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = false ∨ valuation q 93 = false ∨ valuation q 103 = false := by
  rw [value88, value91, value93, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (393 : Vertex) (399 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 88 = true ∨ valuation q 90 = true ∨ valuation q 93 = true ∨ valuation q 103 = true := by
  rw [value88, value90, value91, value93, value103, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(393 : Vertex), (396 : Vertex), (399 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (389 : Vertex) [(393 : Vertex), (396 : Vertex), (399 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 86 = true ∨ valuation q 90 = true ∨ valuation q 93 = true ∨ valuation q 103 = true := by
  rw [value86, value90, value91, value93, value103, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(389 : Vertex), (396 : Vertex), (399 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (393 : Vertex) [(389 : Vertex), (396 : Vertex), (399 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 93 = true ∨ valuation q 103 = true := by
  rw [value86, value88, value91, value93, value103, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(389 : Vertex), (393 : Vertex), (399 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (396 : Vertex) [(389 : Vertex), (393 : Vertex), (399 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 90 = true ∨ valuation q 103 = true := by
  rw [value86, value88, value90, value91, value103, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(389 : Vertex), (393 : Vertex), (396 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (399 : Vertex) [(389 : Vertex), (393 : Vertex), (396 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 90 = true ∨ valuation q 93 = true := by
  rw [value86, value88, value90, value91, value93, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(389 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (413 : Vertex) [(389 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 93 = false := by
  rw [value20, value55, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (270 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 104 = false := by
  rw [value20, value55, value92, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (270 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 20 = false ∨ valuation q 90 = false ∨ valuation q 104 = false := by
  rw [value20, value90, value92, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (396 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 55 = false ∨ valuation q 89 = false ∨ valuation q 93 = false := by
  rw [value55, value89, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (270 : Vertex) (394 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 55 = false ∨ valuation q 93 = false ∨ valuation q 104 = false := by
  rw [value55, value92, value93, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (270 : Vertex) (399 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 93 = false := by
  rw [value89, value90, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (396 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 89 = false ∨ valuation q 93 = false ∨ valuation q 104 = false := by
  rw [value89, value92, value93, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (399 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 115 = false := by
  rw [value90, value92, value93, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (396 : Vertex) (399 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value87, value91, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (391 : Vertex) (397 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 217 = true ∨ valuation q 91 = true ∨ valuation q 92 = true := by
  rw [value91, value92, value93, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(397 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (391 : Vertex) [(397 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 21 = false ∨ valuation q 56 = false ∨ valuation q 95 = false := by
  rw [value21, value56, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (144 : Vertex) (272 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 21 = false ∨ valuation q 56 = false ∨ valuation q 96 = false := by
  rw [value21, value56, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (144 : Vertex) (272 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 21 = false ∨ valuation q 95 = false ∨ valuation q 99 = false := by
  rw [value21, value94, value95, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (144 : Vertex) (401 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 21 = false ∨ valuation q 95 = false ∨ valuation q 116 = false := by
  rw [value21, value94, value95, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (144 : Vertex) (401 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 56 = false ∨ valuation q 82 = false ∨ valuation q 116 = false := by
  rw [value56, value82, value94, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (272 : Vertex) (384 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 56 = false ∨ valuation q 96 = false ∨ valuation q 116 = false := by
  rw [value56, value94, value96, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (272 : Vertex) (402 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 116 = false := by
  rw [value94, value95, value96, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (401 : Vertex) (402 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 83 = false ∨ valuation q 94 = false ∨ valuation q 97 = false := by
  rw [value83, value94, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (385 : Vertex) (400 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E186.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112186
