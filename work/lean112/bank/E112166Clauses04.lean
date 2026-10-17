import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 74 = false := by
  rw [value62, value65, value66, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (322 : Vertex) (331 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 46 = false ∨ valuation q 65 = false ∨ valuation q 75 = false := by
  rw [value46, value65, value66, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (331 : Vertex) (267 : Vertex) (330 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 175 = true ∨ valuation q 46 = true ∨ valuation q 75 = true := by
  rw [value46, value66, value75, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(267 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (330 : Vertex) [(267 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 47 = false ∨ valuation q 63 = false ∨ valuation q 68 = false := by
  rw [value47, value63, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (268 : Vertex) (324 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 176 = true ∨ valuation q 63 = true ∨ valuation q 68 = true := by
  rw [value63, value67, value68, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(324 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (268 : Vertex) [(324 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 176 = true ∨ valuation q 47 = true ∨ valuation q 68 = true := by
  rw [value47, value67, value68, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (324 : Vertex) → w ∈ [(268 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (324 : Vertex) [(268 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 95 = false := by
  rw [value64, value67, value68, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (325 : Vertex) (332 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 177 = true ∨ valuation q 48 = true ∨ valuation q 64 = true ∨ valuation q 67 = true := by
  rw [value48, value64, value67, value68, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(269 : Vertex), (325 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (461 : Vertex) [(269 : Vertex), (325 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 52 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value52, value69, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (337 : Vertex) (273 : Vertex) (341 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 178 = true ∨ valuation q 52 = true ∨ valuation q 70 = true := by
  rw [value52, value69, value70, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(273 : Vertex), (341 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (345 : Vertex) [(273 : Vertex), (341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 64 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value64, value69, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (325 : Vertex) (337 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 179 = true ∨ valuation q 64 = true ∨ valuation q 69 = true := by
  rw [value64, value69, value70, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(325 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (343 : Vertex) [(325 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 180 = true ∨ valuation q 72 = true ∨ valuation q 76 = true := by
  rw [value71, value72, value76, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(343 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (278 : Vertex) [(343 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 180 = true ∨ valuation q 55 = true ∨ valuation q 76 = true := by
  rw [value55, value71, value76, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(278 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (343 : Vertex) [(278 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 180 = true ∨ valuation q 55 = true ∨ valuation q 72 = true := by
  rw [value55, value71, value72, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(278 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (350 : Vertex) [(278 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 182 = true ∨ valuation q 75 = true := by
  rw [value73, value75, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (337 : Vertex) [(347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 182 = true ∨ valuation q 69 = true := by
  rw [value69, value73, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(337 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (347 : Vertex) [(337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 65 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value65, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (330 : Vertex) (347 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 183 = true ∨ valuation q 75 = true ∨ valuation q 76 = true := by
  rw [value74, value75, value76, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(347 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (330 : Vertex) [(347 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 183 = true ∨ valuation q 65 = true ∨ valuation q 76 = true := by
  rw [value65, value74, value76, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(330 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (347 : Vertex) [(330 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 66 = false ∨ valuation q 73 = false ∨ valuation q 74 = false := by
  rw [value66, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (331 : Vertex) (345 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 184 = true ∨ valuation q 73 = true ∨ valuation q 74 = true := by
  rw [value73, value74, value75, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (331 : Vertex) → w ∈ [(345 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (331 : Vertex) [(345 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 59 = false ∨ valuation q 71 = false ∨ valuation q 74 = false := by
  rw [value59, value71, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (286 : Vertex) (342 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 59 = false ∨ valuation q 71 = false ∨ valuation q 98 = false := by
  rw [value59, value71, value76, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (286 : Vertex) (342 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 59 = false ∨ valuation q 74 = false ∨ valuation q 98 = false := by
  rw [value59, value74, value76, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (286 : Vertex) (346 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 86 = false := by
  rw [value77, value78, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (419 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 187 = true ∨ valuation q 80 = true ∨ valuation q 88 = true := by
  rw [value78, value80, value88, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (417 : Vertex) [(427 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 187 = true ∨ valuation q 77 = true ∨ valuation q 88 = true := by
  rw [value77, value78, value88, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(417 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (427 : Vertex) [(417 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 187 = true ∨ valuation q 77 = true ∨ valuation q 80 = true := by
  rw [value77, value78, value80, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(417 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (435 : Vertex) [(417 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 188 = true ∨ valuation q 15 = true ∨ valuation q 77 = true ∨ valuation q 82 = true := by
  rw [value15, value77, value79, value82, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(165 : Vertex), (417 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (485 : Vertex) [(165 : Vertex), (417 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 17 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value17, value78, value80, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (419 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 78 = false ∨ valuation q 84 = false ∨ valuation q 101 = false := by
  rw [value78, value80, value84, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (419 : Vertex) (431 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E166.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112166
