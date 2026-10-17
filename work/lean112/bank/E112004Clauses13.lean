import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 52 = false ∨ valuation q 56 = false := by
  rw [value15, value52, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (186 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 52 = false ∨ valuation q 73 = false := by
  rw [value15, value52, value55, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (186 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 52 = false ∨ valuation q 103 = false := by
  rw [value15, value52, value55, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (186 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value15, value53, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 53 = false ∨ valuation q 73 = false := by
  rw [value15, value53, value55, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (188 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 53 = false ∨ valuation q 103 = false := by
  rw [value15, value53, value55, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (188 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 56 = false ∨ valuation q 73 = false := by
  rw [value15, value55, value56, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (191 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 56 = false ∨ valuation q 103 = false := by
  rw [value15, value55, value56, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (191 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 73 = false ∨ valuation q 103 = false := by
  rw [value15, value55, value73, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (254 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value48, value52, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (186 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 56 = false := by
  rw [value48, value52, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (186 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 73 = false := by
  rw [value48, value52, value55, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (186 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 103 = false := by
  rw [value48, value52, value55, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (186 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value48, value53, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 73 = false := by
  rw [value48, value53, value55, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (188 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 103 = false := by
  rw [value48, value53, value55, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (188 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 48 = false ∨ valuation q 56 = false ∨ valuation q 73 = false := by
  rw [value48, value55, value56, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (191 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 48 = false ∨ valuation q 56 = false ∨ valuation q 103 = false := by
  rw [value48, value55, value56, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (191 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 48 = false ∨ valuation q 73 = false ∨ valuation q 103 = false := by
  rw [value48, value55, value73, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (254 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value52, value53, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (186 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 73 = false := by
  rw [value52, value53, value55, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (186 : Vertex) (188 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 103 = false := by
  rw [value52, value53, value55, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (186 : Vertex) (188 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 56 = false ∨ valuation q 73 = false := by
  rw [value52, value55, value56, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (186 : Vertex) (191 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 56 = false ∨ valuation q 103 = false := by
  rw [value52, value55, value56, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (186 : Vertex) (191 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 73 = false ∨ valuation q 103 = false := by
  rw [value52, value55, value73, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (186 : Vertex) (254 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 73 = false := by
  rw [value53, value55, value56, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (188 : Vertex) (191 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 103 = false := by
  rw [value53, value55, value56, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (188 : Vertex) (191 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 53 = false ∨ valuation q 73 = false ∨ valuation q 103 = false := by
  rw [value53, value55, value73, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (188 : Vertex) (254 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 73 = false ∨ valuation q 103 = false := by
  rw [value55, value56, value73, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (191 : Vertex) (254 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 175 = true ∨ valuation q 15 = true ∨ valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 56 = true ∨ valuation q 73 = true ∨ valuation q 103 = true := by
  rw [value15, value52, value53, value55, value56, value73, value103, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(62 : Vertex), (186 : Vertex), (188 : Vertex), (191 : Vertex), (254 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (182 : Vertex) [(62 : Vertex), (186 : Vertex), (188 : Vertex), (191 : Vertex), (254 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 175 = true ∨ valuation q 15 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 56 = true ∨ valuation q 103 = true := by
  rw [value15, value48, value52, value53, value55, value56, value103, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(62 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (191 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (254 : Vertex) [(62 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (191 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 175 = true ∨ valuation q 15 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 56 = true ∨ valuation q 73 = true := by
  rw [value15, value48, value52, value53, value55, value56, value73, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(62 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (191 : Vertex), (254 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (446 : Vertex) [(62 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (191 : Vertex), (254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block13 (q : Snake 81) (h : Conditions q) : B112E004.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112004
