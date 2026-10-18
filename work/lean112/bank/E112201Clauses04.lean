import E112201Semantics
import B112E201Inputs
namespace Snake9.Regrowth.E112201
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 74 = false := by
  rw [value61, value64, value65, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 175 = true ∨ valuation q 62 = true := by
  rw [value62, value66, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (364 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(356 : Vertex)] := by decide
  have hg := other_cover q (364 : Vertex) (366 : Vertex) [(356 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 57 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value57, value68, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (304 : Vertex) (372 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 57 = false ∨ valuation q 72 = false ∨ valuation q 100 = false := by
  rw [value57, value68, value72, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (304 : Vertex) (376 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 63 = false ∨ valuation q 69 = false ∨ valuation q 71 = false := by
  rw [value63, value69, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (357 : Vertex) (372 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 70 = true ∨ valuation q 75 = true := by
  rw [value70, value71, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ∈ [(373 : Vertex), (383 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (375 : Vertex) [(373 : Vertex), (383 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 180 = true ∨ valuation q 70 = true := by
  rw [value70, value71, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(373 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (383 : Vertex) [(373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 181 = true ∨ valuation q 73 = true := by
  rw [value72, value73, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(377 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (368 : Vertex) [(377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 181 = true ∨ valuation q 68 = true := by
  rw [value68, value72, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(368 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (377 : Vertex) [(368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 65 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value65, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (363 : Vertex) (377 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 15 = false ∨ valuation q 77 = false ∨ valuation q 80 = false := by
  rw [value15, value76, value77, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (162 : Vertex) (419 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 186 = true ∨ valuation q 16 = true ∨ valuation q 76 = true ∨ valuation q 81 = true := by
  rw [value16, value76, value77, value81, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (291 : Vertex) → w ∈ [(163 : Vertex), (418 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (291 : Vertex) [(163 : Vertex), (418 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value78, value79, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 17 = false ∨ valuation q 78 = false ∨ valuation q 86 = false := by
  rw [value17, value78, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (420 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 189 = true ∨ valuation q 76 = true ∨ valuation q 81 = true ∨ valuation q 90 = true := by
  rw [value76, value80, value81, value90, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(418 : Vertex), (427 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (430 : Vertex) [(418 : Vertex), (427 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 19 = false ∨ valuation q 77 = false ∨ valuation q 91 = false := by
  rw [value19, value77, value81, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (419 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 77 = false ∨ valuation q 80 = false ∨ valuation q 91 = false := by
  rw [value77, value80, value81, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (419 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 191 = true ∨ valuation q 83 = true := by
  rw [value82, value83, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(430 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (420 : Vertex) [(430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 191 = true ∨ valuation q 78 = true := by
  rw [value78, value82, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(420 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (430 : Vertex) [(420 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 192 = true ∨ valuation q 80 = true := by
  rw [value80, value83, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(426 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (428 : Vertex) [(426 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 22 = false ∨ valuation q 85 = false ∨ valuation q 88 = false := by
  rw [value22, value84, value85, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (176 : Vertex) (436 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 57 = false ∨ valuation q 85 = false ∨ valuation q 88 = false := by
  rw [value57, value84, value85, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (304 : Vertex) (436 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 79 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value79, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (436 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 196 = true ∨ valuation q 92 = true := by
  rw [value87, value92, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (437 : Vertex) [(447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 196 = true ∨ valuation q 86 = true := by
  rw [value86, value87, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(437 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (447 : Vertex) [(437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 197 = true ∨ valuation q 27 = true ∨ valuation q 84 = true ∨ valuation q 90 = true := by
  rw [value27, value84, value88, value90, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(184 : Vertex), (432 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (441 : Vertex) [(184 : Vertex), (432 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 197 = true ∨ valuation q 27 = true ∨ valuation q 84 = true ∨ valuation q 89 = true := by
  rw [value27, value84, value88, value89, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(184 : Vertex), (432 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (442 : Vertex) [(184 : Vertex), (432 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 80 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value80, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 200 = true ∨ valuation q 81 = true ∨ valuation q 90 = true ∨ valuation q 92 = true := by
  rw [value81, value90, value91, value92, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(427 : Vertex), (442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (441 : Vertex) [(427 : Vertex), (442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 31 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value31, value87, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (191 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 201 = true ∨ valuation q 31 = true ∨ valuation q 91 = true := by
  rw [value31, value91, value92, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(191 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (439 : Vertex) [(191 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 201 = true ∨ valuation q 31 = true ∨ valuation q 87 = true := by
  rw [value31, value87, value92, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(191 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (443 : Vertex) [(191 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E201.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112201
