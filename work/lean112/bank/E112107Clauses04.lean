import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 47 = true ∨ valuation q 64 = true ∨ valuation q 65 = true ∨ valuation q 70 = true := by
  rw [value47, value64, value65, value66, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ∈ [(263 : Vertex), (325 : Vertex), (326 : Vertex), (335 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (327 : Vertex) [(263 : Vertex), (325 : Vertex), (326 : Vertex), (335 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 47 = false ∨ valuation q 65 = false ∨ valuation q 70 = false := by
  rw [value47, value65, value66, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (263 : Vertex) (326 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 176 = true ∨ valuation q 64 = true ∨ valuation q 65 = true ∨ valuation q 70 = true := by
  rw [value64, value65, value66, value70, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(325 : Vertex), (326 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (263 : Vertex) [(325 : Vertex), (326 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 176 = true ∨ valuation q 47 = true ∨ valuation q 64 = true ∨ valuation q 70 = true := by
  rw [value47, value64, value66, value70, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(263 : Vertex), (325 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (326 : Vertex) [(263 : Vertex), (325 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 176 = true ∨ valuation q 47 = true ∨ valuation q 64 = true ∨ valuation q 65 = true := by
  rw [value47, value64, value65, value66, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(263 : Vertex), (325 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (335 : Vertex) [(263 : Vertex), (325 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 67 = true := by
  rw [value67, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (328 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 48 = false ∨ valuation q 62 = false ∨ valuation q 98 = false := by
  rw [value48, value62, value67, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (264 : Vertex) (320 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 62 = false ∨ valuation q 98 = false := by
  rw [value62, value98, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (328 : Vertex) (320 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 177 = true ∨ valuation q 48 = true ∨ valuation q 68 = true ∨ valuation q 98 = true := by
  rw [value48, value67, value68, value98, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(264 : Vertex), (329 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (320 : Vertex) [(264 : Vertex), (329 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 177 = true ∨ valuation q 48 = true ∨ valuation q 62 = true ∨ valuation q 68 = true := by
  rw [value48, value62, value67, value68, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(264 : Vertex), (320 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (456 : Vertex) [(264 : Vertex), (320 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 49 = false ∨ valuation q 63 = false ∨ valuation q 67 = false := by
  rw [value49, value63, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (265 : Vertex) (321 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 49 = false ∨ valuation q 63 = false ∨ valuation q 69 = false := by
  rw [value49, value63, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (265 : Vertex) (321 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 49 = false ∨ valuation q 67 = false ∨ valuation q 69 = false := by
  rw [value49, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (265 : Vertex) (328 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 63 = false ∨ valuation q 67 = false ∨ valuation q 69 = false := by
  rw [value63, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (328 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 178 = true ∨ valuation q 49 = true ∨ valuation q 63 = true ∨ valuation q 67 = true := by
  rw [value49, value63, value67, value68, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(265 : Vertex), (321 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (333 : Vertex) [(265 : Vertex), (321 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 69 = true := by
  rw [value69, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (333 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 64 = true ∨ valuation q 68 = true ∨ valuation q 70 = true ∨ valuation q 77 = true := by
  rw [value64, value68, value69, value70, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ∈ [(325 : Vertex), (329 : Vertex), (335 : Vertex), (349 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (333 : Vertex) [(325 : Vertex), (329 : Vertex), (335 : Vertex), (349 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 64 = false ∨ valuation q 68 = false ∨ valuation q 77 = false := by
  rw [value64, value68, value69, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (325 : Vertex) (329 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 77 = false := by
  rw [value68, value69, value70, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (329 : Vertex) (335 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 179 = true ∨ valuation q 68 = true ∨ valuation q 70 = true ∨ valuation q 77 = true := by
  rw [value68, value69, value70, value77, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(329 : Vertex), (335 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (325 : Vertex) [(329 : Vertex), (335 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 179 = true ∨ valuation q 64 = true ∨ valuation q 70 = true ∨ valuation q 77 = true := by
  rw [value64, value69, value70, value77, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(325 : Vertex), (335 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (329 : Vertex) [(325 : Vertex), (335 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 179 = true ∨ valuation q 64 = true ∨ valuation q 68 = true ∨ valuation q 77 = true := by
  rw [value64, value68, value69, value77, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(325 : Vertex), (329 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (335 : Vertex) [(325 : Vertex), (329 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 179 = true ∨ valuation q 64 = true ∨ valuation q 68 = true ∨ valuation q 70 = true := by
  rw [value64, value68, value69, value70, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(325 : Vertex), (329 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (349 : Vertex) [(325 : Vertex), (329 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 180 = true ∨ valuation q 66 = true := by
  rw [value66, value70, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(327 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (333 : Vertex) [(327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 181 = true ∨ valuation q 73 = true := by
  rw [value71, value73, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(339 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (321 : Vertex) [(339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 181 = true ∨ valuation q 63 = true := by
  rw [value63, value71, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(321 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (339 : Vertex) [(321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value72, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (339 : Vertex) (342 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 71 = true ∨ valuation q 72 = true := by
  rw [value71, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ∈ [(337 : Vertex), (338 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (339 : Vertex) [(337 : Vertex), (338 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value71, value72, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (339 : Vertex) (337 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 183 = true ∨ valuation q 72 = true := by
  rw [value72, value73, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(338 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (337 : Vertex) [(338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 183 = true ∨ valuation q 71 = true := by
  rw [value71, value73, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(337 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (338 : Vertex) [(337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 65 = false ∨ valuation q 72 = false ∨ valuation q 78 = false := by
  rw [value65, value72, value74, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (326 : Vertex) (338 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E107.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112107
