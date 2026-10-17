import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 68 = false := by
  rw [value48, value51, value52, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (271 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 85 = false := by
  rw [value48, value51, value52, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (271 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 48 = false ∨ valuation q 68 = false ∨ valuation q 85 = false := by
  rw [value48, value51, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (333 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 68 = false := by
  rw [value50, value51, value52, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (268 : Vertex) (271 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 85 = false := by
  rw [value50, value51, value52, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (268 : Vertex) (271 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 68 = false ∨ valuation q 85 = false := by
  rw [value50, value51, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (268 : Vertex) (333 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 68 = false ∨ valuation q 85 = false := by
  rw [value51, value52, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (271 : Vertex) (333 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 49 = false ∨ valuation q 59 = false := by
  rw [value47, value49, value52, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 59 = false := by
  rw [value49, value51, value52, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (269 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 161 = true ∨ valuation q 49 = true ∨ valuation q 51 = true ∨ valuation q 59 = true := by
  rw [value49, value51, value52, value59, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(267 : Vertex), (269 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (263 : Vertex) [(267 : Vertex), (269 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 162 = true ∨ valuation q 55 = true ∨ valuation q 56 = true := by
  rw [value53, value55, value56, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (273 : Vertex) → w ∈ [(274 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (273 : Vertex) [(274 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 162 = true ∨ valuation q 54 = true ∨ valuation q 55 = true := by
  rw [value53, value54, value55, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(273 : Vertex), (274 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (276 : Vertex) [(273 : Vertex), (274 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 44 = false ∨ valuation q 53 = false ∨ valuation q 69 = false := by
  rw [value44, value53, value54, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (257 : Vertex) (272 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 163 = true ∨ valuation q 44 = true ∨ valuation q 69 = true ∨ valuation q 86 = true := by
  rw [value44, value54, value69, value86, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (273 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(257 : Vertex), (337 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (273 : Vertex) (272 : Vertex) [(257 : Vertex), (337 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 163 = true ∨ valuation q 44 = true ∨ valuation q 53 = true ∨ valuation q 86 = true := by
  rw [value44, value53, value54, value86, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (273 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(257 : Vertex), (272 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (273 : Vertex) (337 : Vertex) [(257 : Vertex), (272 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 164 = true := by
  rw [value55, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (274 : Vertex) (272 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 165 = true ∨ valuation q 57 = true := by
  rw [value56, value57, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(284 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (272 : Vertex) [(284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 165 = true ∨ valuation q 53 = true := by
  rw [value53, value56, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(272 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (284 : Vertex) [(272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 50 = false ∨ valuation q 56 = false ∨ valuation q 58 = false := by
  rw [value50, value56, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (268 : Vertex) (276 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 166 = true ∨ valuation q 50 = true ∨ valuation q 58 = true := by
  rw [value50, value57, value58, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(268 : Vertex), (286 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (276 : Vertex) [(268 : Vertex), (286 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 166 = true ∨ valuation q 50 = true ∨ valuation q 56 = true := by
  rw [value50, value56, value57, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (286 : Vertex) → w ∈ [(268 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (286 : Vertex) [(268 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 167 = true ∨ valuation q 59 = true := by
  rw [value58, value59, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(287 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (284 : Vertex) [(287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 167 = true ∨ valuation q 57 = true := by
  rw [value57, value58, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(284 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (287 : Vertex) [(284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 168 = true ∨ valuation q 58 = true := by
  rw [value58, value59, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(286 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (271 : Vertex) [(286 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 168 = true ∨ valuation q 52 = true := by
  rw [value52, value59, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (286 : Vertex) → w ∈ [(271 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (286 : Vertex) [(271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 169 = true ∨ valuation q 61 = true := by
  rw [value60, value61, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (324 : Vertex) → w ∈ [(322 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (324 : Vertex) [(322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 45 = false ∨ valuation q 61 = false ∨ valuation q 66 = false := by
  rw [value45, value61, value62, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (259 : Vertex) (322 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 171 = true ∨ valuation q 45 = true ∨ valuation q 61 = true := by
  rw [value45, value61, value62, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (323 : Vertex) w → w ∈ region → w ≠ (331 : Vertex) → w ∈ [(259 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (323 : Vertex) (331 : Vertex) [(259 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 172 = true ∨ valuation q 64 = true ∨ valuation q 67 = true := by
  rw [value63, value64, value67, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(326 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (320 : Vertex) [(326 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 172 = true ∨ valuation q 60 = true ∨ valuation q 67 = true := by
  rw [value60, value63, value67, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(320 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (326 : Vertex) [(320 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 172 = true ∨ valuation q 60 = true ∨ valuation q 64 = true := by
  rw [value60, value63, value64, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(320 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (332 : Vertex) [(320 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 71 = false := by
  rw [value61, value63, value64, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (322 : Vertex) (324 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E090.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112090
