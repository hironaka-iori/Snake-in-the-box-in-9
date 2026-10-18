import E112148Semantics
import B112E148Inputs
namespace Snake9.Regrowth.E112148
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 168 = true ∨ valuation q 91 = true := by
  rw [value57, value91, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(417 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (288 : Vertex) [(417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 169 = true ∨ valuation q 61 = true := by
  rw [value58, value61, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (294 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(302 : Vertex)] := by decide
  have hg := other_cover q (294 : Vertex) (310 : Vertex) [(302 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 170 = true ∨ valuation q 56 = true := by
  rw [value56, value59, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (300 : Vertex) → w ∈ [(288 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (300 : Vertex) [(288 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 171 = true ∨ valuation q 59 = true := by
  rw [value59, value60, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (300 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(296 : Vertex)] := by decide
  have hg := other_cover q (300 : Vertex) (302 : Vertex) [(296 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 172 = true ∨ valuation q 60 = true := by
  rw [value60, value61, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(300 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (294 : Vertex) [(300 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 58 = true := by
  rw [value58, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ∈ [(294 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (310 : Vertex) [(294 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 62 = true := by
  rw [value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 175 = true ∨ valuation q 4 = true ∨ valuation q 68 = true := by
  rw [value4, value64, value68, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(65 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(65 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 71 = false ∨ valuation q 75 = false := by
  rw [value65, value66, value71, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (327 : Vertex) (334 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 177 = true ∨ valuation q 7 = true ∨ valuation q 76 = true := by
  rw [value7, value66, value76, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(71 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (326 : Vertex) [(71 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 177 = true ∨ valuation q 7 = true ∨ valuation q 65 = true := by
  rw [value7, value65, value66, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(71 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (343 : Vertex) [(71 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 178 = true ∨ valuation q 68 = true ∨ valuation q 70 = true := by
  rw [value67, value68, value70, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(329 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (320 : Vertex) [(329 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 69 = false := by
  rw [value64, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (328 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 77 = false := by
  rw [value64, value67, value68, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (328 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 67 = false ∨ valuation q 69 = false ∨ valuation q 77 = false := by
  rw [value67, value68, value69, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (328 : Vertex) (331 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 180 = true ∨ valuation q 68 = true ∨ valuation q 79 = true := by
  rw [value68, value69, value79, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(329 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (75 : Vertex) [(329 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 180 = true ∨ valuation q 8 = true ∨ valuation q 79 = true := by
  rw [value8, value69, value79, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(75 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (329 : Vertex) [(75 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 180 = true ∨ valuation q 8 = true ∨ valuation q 68 = true := by
  rw [value8, value68, value69, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(75 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (347 : Vertex) [(75 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 181 = true ∨ valuation q 71 = true := by
  rw [value70, value71, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(334 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (328 : Vertex) [(334 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 182 = true ∨ valuation q 65 = true := by
  rw [value65, value71, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(326 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (332 : Vertex) [(326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 13 = false ∨ valuation q 75 = false ∨ valuation q 78 = false := by
  rw [value13, value72, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (82 : Vertex) (342 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 15 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value15, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (84 : Vertex) (341 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 188 = true ∨ valuation q 68 = true ∨ valuation q 79 = true := by
  rw [value68, value77, value79, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(329 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (349 : Vertex) [(329 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 189 = true ∨ valuation q 72 = true ∨ valuation q 79 = true := by
  rw [value72, value78, value79, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(338 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (90 : Vertex) [(338 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 189 = true ∨ valuation q 17 = true ∨ valuation q 79 = true := by
  rw [value17, value78, value79, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(90 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (338 : Vertex) [(90 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 189 = true ∨ valuation q 17 = true ∨ valuation q 72 = true := by
  rw [value17, value72, value78, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(90 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (347 : Vertex) [(90 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 69 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value69, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (331 : Vertex) (345 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 192 = true ∨ valuation q 22 = true ∨ valuation q 83 = true := by
  rw [value22, value81, value83, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(129 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (417 : Vertex) [(129 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 193 = true ∨ valuation q 87 = true := by
  rw [value82, value87, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(407 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (135 : Vertex) [(407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 193 = true ∨ valuation q 25 = true := by
  rw [value25, value82, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(135 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (407 : Vertex) [(135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 26 = false ∨ valuation q 81 = false ∨ valuation q 88 = false := by
  rw [value26, value81, value83, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (385 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 194 = true ∨ valuation q 26 = true ∨ valuation q 81 = true := by
  rw [value26, value81, value83, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (393 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(137 : Vertex), (385 : Vertex)] := by decide
  have hg := other_cover q (393 : Vertex) (409 : Vertex) [(137 : Vertex), (385 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E148.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112148
