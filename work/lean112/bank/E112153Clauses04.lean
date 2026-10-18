import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 170 = true ∨ valuation q 36 = true ∨ valuation q 124 = true := by
  rw [value36, value46, value124, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(206 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (220 : Vertex) [(206 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 170 = true ∨ valuation q 36 = true ∨ valuation q 44 = true := by
  rw [value36, value44, value46, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(206 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (478 : Vertex) [(206 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 171 = true ∨ valuation q 49 = true := by
  rw [value47, value49, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(261 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (259 : Vertex) [(261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 171 = true ∨ valuation q 48 = true := by
  rw [value47, value48, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(259 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (261 : Vertex) [(259 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 172 = true ∨ valuation q 47 = true ∨ valuation q 53 = true := by
  rw [value47, value48, value53, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(257 : Vertex), (267 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (263 : Vertex) [(257 : Vertex), (267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 172 = true ∨ valuation q 47 = true ∨ valuation q 51 = true := by
  rw [value47, value48, value51, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(257 : Vertex), (263 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (267 : Vertex) [(257 : Vertex), (263 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 3 = false ∨ valuation q 47 = false ∨ valuation q 55 = false := by
  rw [value3, value47, value49, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (5 : Vertex) (257 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 3 = false ∨ valuation q 47 = false ∨ valuation q 60 = false := by
  rw [value3, value47, value49, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (5 : Vertex) (257 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 3 = false ∨ valuation q 51 = false ∨ valuation q 55 = false := by
  rw [value3, value49, value51, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (5 : Vertex) (263 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 47 = false ∨ valuation q 55 = false ∨ valuation q 60 = false := by
  rw [value47, value49, value55, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (257 : Vertex) (269 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 60 = false := by
  rw [value49, value51, value55, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (263 : Vertex) (269 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 4 = false ∨ valuation q 51 = false ∨ valuation q 61 = false := by
  rw [value4, value50, value51, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (263 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 4 = false ∨ valuation q 61 = false ∨ valuation q 68 = false := by
  rw [value4, value50, value61, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (278 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 61 = false ∨ valuation q 68 = false := by
  rw [value50, value51, value61, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (263 : Vertex) (278 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value48, value49, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (259 : Vertex) (261 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 48 = false ∨ valuation q 69 = false ∨ valuation q 85 = false := by
  rw [value48, value51, value69, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (259 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 175 = true ∨ valuation q 49 = true ∨ valuation q 50 = true ∨ valuation q 56 = true ∨ valuation q 69 = true ∨ valuation q 85 = true := by
  rw [value49, value50, value51, value56, value69, value85, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex), (271 : Vertex), (327 : Vertex), (391 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (259 : Vertex) [(261 : Vertex), (262 : Vertex), (271 : Vertex), (327 : Vertex), (391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 62 = false ∨ valuation q 70 = false := by
  rw [value52, value54, value62, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (268 : Vertex) (280 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 176 = true ∨ valuation q 62 = true ∨ valuation q 70 = true := by
  rw [value52, value62, value70, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(280 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (268 : Vertex) [(280 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 176 = true ∨ valuation q 54 = true ∨ valuation q 70 = true := by
  rw [value52, value54, value70, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(268 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (280 : Vertex) [(268 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 176 = true ∨ valuation q 54 = true ∨ valuation q 62 = true := by
  rw [value52, value54, value62, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(268 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (328 : Vertex) [(268 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 177 = true ∨ valuation q 56 = true ∨ valuation q 64 = true := by
  rw [value53, value56, value64, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(271 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (259 : Vertex) [(271 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 177 = true ∨ valuation q 48 = true ∨ valuation q 64 = true := by
  rw [value48, value53, value64, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(259 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (271 : Vertex) [(259 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 177 = true ∨ valuation q 48 = true ∨ valuation q 56 = true := by
  rw [value48, value53, value56, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(259 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (283 : Vertex) [(259 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 5 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value5, value52, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (264 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 5 = false ∨ valuation q 52 = false ∨ valuation q 88 = false := by
  rw [value5, value52, value54, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (264 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 88 = false := by
  rw [value52, value54, value55, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (264 : Vertex) (269 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = false ∨ valuation q 54 = false ∨ valuation q 89 = false := by
  rw [value49, value54, value55, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (268 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 89 = false := by
  rw [value49, value55, value56, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (271 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 179 = true ∨ valuation q 54 = true ∨ valuation q 56 = true ∨ valuation q 89 = true := by
  rw [value54, value55, value56, value89, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (269 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(268 : Vertex), (271 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (269 : Vertex) (261 : Vertex) [(268 : Vertex), (271 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 179 = true ∨ valuation q 49 = true ∨ valuation q 56 = true ∨ valuation q 89 = true := by
  rw [value49, value55, value56, value89, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (269 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(261 : Vertex), (271 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (269 : Vertex) (268 : Vertex) [(261 : Vertex), (271 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 179 = true ∨ valuation q 49 = true ∨ valuation q 54 = true ∨ valuation q 89 = true := by
  rw [value49, value54, value55, value89, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (269 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(261 : Vertex), (268 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (269 : Vertex) (271 : Vertex) [(261 : Vertex), (268 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E153.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112153
