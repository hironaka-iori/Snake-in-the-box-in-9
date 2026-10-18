import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 93 = false ∨ valuation q 112 = false := by
  rw [value47, value92, value93, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (423 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 98 = false ∨ valuation q 112 = false := by
  rw [value47, value92, value98, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 71 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value71, value89, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (418 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 71 = false ∨ valuation q 89 = false ∨ valuation q 93 = false := by
  rw [value71, value89, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (418 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 71 = false ∨ valuation q 89 = false ∨ valuation q 98 = false := by
  rw [value71, value89, value92, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (418 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 71 = false ∨ valuation q 89 = false ∨ valuation q 112 = false := by
  rw [value71, value89, value92, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (418 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 71 = false ∨ valuation q 90 = false ∨ valuation q 93 = false := by
  rw [value71, value90, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 71 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value71, value90, value92, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (420 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 71 = false ∨ valuation q 90 = false ∨ valuation q 112 = false := by
  rw [value71, value90, value92, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (420 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 71 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value71, value92, value93, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 71 = false ∨ valuation q 93 = false ∨ valuation q 112 = false := by
  rw [value71, value92, value93, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (423 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 71 = false ∨ valuation q 98 = false ∨ valuation q 112 = false := by
  rw [value71, value92, value98, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 93 = false := by
  rw [value89, value90, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (418 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value89, value90, value92, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (418 : Vertex) (420 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 112 = false := by
  rw [value89, value90, value92, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (418 : Vertex) (420 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 89 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value89, value92, value93, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (418 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 89 = false ∨ valuation q 93 = false ∨ valuation q 112 = false := by
  rw [value89, value92, value93, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (418 : Vertex) (423 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 112 = false := by
  rw [value89, value92, value98, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (418 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value90, value92, value93, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (420 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 112 = false := by
  rw [value90, value92, value93, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (420 : Vertex) (423 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 90 = false ∨ valuation q 98 = false ∨ valuation q 112 = false := by
  rw [value90, value92, value98, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (420 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 112 = false := by
  rw [value92, value93, value98, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (423 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 72 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value72, value91, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 72 = false ∨ valuation q 91 = false ∨ valuation q 99 = false := by
  rw [value72, value91, value93, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (421 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 72 = false ∨ valuation q 92 = false ∨ valuation q 104 = false := by
  rw [value72, value92, value93, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (422 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 99 = false := by
  rw [value91, value92, value93, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (422 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 113 = false := by
  rw [value91, value92, value93, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (422 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 219 = true ∨ valuation q 72 = true ∨ valuation q 91 = true ∨ valuation q 92 = true ∨ valuation q 99 = true ∨ valuation q 104 = true := by
  rw [value72, value91, value92, value93, value99, value104, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (423 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(295 : Vertex), (421 : Vertex), (422 : Vertex), (431 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (423 : Vertex) (487 : Vertex) [(295 : Vertex), (421 : Vertex), (422 : Vertex), (431 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 48 = false ∨ valuation q 73 = false ∨ valuation q 114 = false := by
  rw [value48, value73, value94, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 48 = false ∨ valuation q 87 = false ∨ valuation q 97 = false := by
  rw [value48, value87, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (416 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 48 = false ∨ valuation q 95 = false ∨ valuation q 114 = false := by
  rw [value48, value94, value95, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (426 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 48 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value48, value94, value97, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E121.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112121
