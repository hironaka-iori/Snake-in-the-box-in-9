import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 3 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value3, value65, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (101 : Vertex) (356 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 182 = true ∨ valuation q 63 = true ∨ valuation q 65 = true ∨ valuation q 68 = true ∨ valuation q 78 = true := by
  rw [value63, value65, value66, value68, value78, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (101 : Vertex) → w ∈ [(353 : Vertex), (356 : Vertex), (359 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (101 : Vertex) [(353 : Vertex), (356 : Vertex), (359 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 47 = false ∨ valuation q 65 = false ∨ valuation q 102 = false := by
  rw [value47, value65, value67, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (358 : Vertex) (294 : Vertex) (356 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value64, value65, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (358 : Vertex) (354 : Vertex) (356 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 73 = false := by
  rw [value65, value67, value68, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (358 : Vertex) (356 : Vertex) (359 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 48 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value48, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (357 : Vertex) (358 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 48 = false ∨ valuation q 66 = false ∨ valuation q 74 = false := by
  rw [value48, value66, value68, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (357 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 48 = false ∨ valuation q 66 = false ∨ valuation q 79 = false := by
  rw [value48, value66, value68, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (357 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 48 = false ∨ valuation q 67 = false ∨ valuation q 74 = false := by
  rw [value48, value67, value68, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (358 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 48 = false ∨ valuation q 67 = false ∨ valuation q 79 = false := by
  rw [value48, value67, value68, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (358 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 48 = false ∨ valuation q 67 = false ∨ valuation q 103 = false := by
  rw [value48, value67, value68, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (358 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 48 = false ∨ valuation q 74 = false ∨ valuation q 79 = false := by
  rw [value48, value68, value74, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (367 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 48 = false ∨ valuation q 79 = false ∨ valuation q 103 = false := by
  rw [value48, value68, value79, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (375 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 74 = false := by
  rw [value66, value67, value68, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (357 : Vertex) (358 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 79 = false := by
  rw [value66, value67, value68, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (357 : Vertex) (358 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 103 = false := by
  rw [value66, value67, value68, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (357 : Vertex) (358 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 66 = false ∨ valuation q 74 = false ∨ valuation q 79 = false := by
  rw [value66, value68, value74, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (357 : Vertex) (367 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 66 = false ∨ valuation q 79 = false ∨ valuation q 103 = false := by
  rw [value66, value68, value79, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (357 : Vertex) (375 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 67 = false ∨ valuation q 74 = false ∨ valuation q 79 = false := by
  rw [value67, value68, value74, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (358 : Vertex) (367 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 74 = false ∨ valuation q 79 = false ∨ valuation q 103 = false := by
  rw [value68, value74, value79, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (367 : Vertex) (375 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 49 = false ∨ valuation q 62 = false ∨ valuation q 70 = false := by
  rw [value49, value62, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (352 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 49 = false ∨ valuation q 62 = false ∨ valuation q 72 = false := by
  rw [value49, value62, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (352 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 49 = false ∨ valuation q 62 = false ∨ valuation q 104 = false := by
  rw [value49, value62, value69, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (352 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 49 = false ∨ valuation q 70 = false ∨ valuation q 72 = false := by
  rw [value49, value69, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (362 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 49 = false ∨ valuation q 70 = false ∨ valuation q 104 = false := by
  rw [value49, value69, value70, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (362 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 49 = false ∨ valuation q 72 = false ∨ valuation q 104 = false := by
  rw [value49, value69, value72, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (364 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 62 = false ∨ valuation q 70 = false ∨ valuation q 72 = false := by
  rw [value62, value69, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (352 : Vertex) (362 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 62 = false ∨ valuation q 70 = false ∨ valuation q 104 = false := by
  rw [value62, value69, value70, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (352 : Vertex) (362 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 62 = false ∨ valuation q 72 = false ∨ valuation q 104 = false := by
  rw [value62, value69, value72, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (352 : Vertex) (364 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 104 = false := by
  rw [value69, value70, value72, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (362 : Vertex) (364 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 81 = false := by
  rw [value69, value70, value71, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (362 : Vertex) (360 : Vertex) (363 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 186 = true ∨ valuation q 64 = true ∨ valuation q 71 = true ∨ valuation q 73 = true ∨ valuation q 81 = true := by
  rw [value64, value70, value71, value73, value81, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(354 : Vertex), (363 : Vertex), (366 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (360 : Vertex) [(354 : Vertex), (363 : Vertex), (366 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E058.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112058
