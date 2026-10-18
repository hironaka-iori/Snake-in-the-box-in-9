import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 164 = true ∨ valuation q 37 = true ∨ valuation q 47 = true ∨ valuation q 69 = true := by
  rw [value37, value47, value48, value69, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(131 : Vertex), (145 : Vertex), (179 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (155 : Vertex) [(131 : Vertex), (145 : Vertex), (179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 164 = true ∨ valuation q 37 = true ∨ valuation q 47 = true ∨ valuation q 53 = true := by
  rw [value37, value47, value48, value53, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(131 : Vertex), (145 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (179 : Vertex) [(131 : Vertex), (145 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 13 = false ∨ valuation q 38 = false ∨ valuation q 47 = false := by
  rw [value13, value38, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (21 : Vertex) (133 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 13 = false ∨ valuation q 38 = false ∨ valuation q 55 = false := by
  rw [value13, value38, value49, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (21 : Vertex) (133 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 165 = true ∨ valuation q 38 = true ∨ valuation q 47 = true ∨ valuation q 55 = true := by
  rw [value38, value47, value49, value55, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(133 : Vertex), (145 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (21 : Vertex) [(133 : Vertex), (145 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 165 = true ∨ valuation q 13 = true ∨ valuation q 38 = true ∨ valuation q 55 = true := by
  rw [value13, value38, value49, value55, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(21 : Vertex), (133 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (145 : Vertex) [(21 : Vertex), (133 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 166 = true ∨ valuation q 39 = true ∨ valuation q 56 = true := by
  rw [value39, value50, value56, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(134 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (22 : Vertex) [(134 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 166 = true ∨ valuation q 14 = true ∨ valuation q 56 = true := by
  rw [value14, value50, value56, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(22 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (134 : Vertex) [(22 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 166 = true ∨ valuation q 14 = true ∨ valuation q 39 = true := by
  rw [value14, value39, value50, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(22 : Vertex), (134 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (158 : Vertex) [(22 : Vertex), (134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 15 = false ∨ valuation q 46 = false ∨ valuation q 52 = false := by
  rw [value15, value46, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (24 : Vertex) (144 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 15 = false ∨ valuation q 46 = false ∨ valuation q 54 = false := by
  rw [value15, value46, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (24 : Vertex) (144 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 15 = false ∨ valuation q 46 = false ∨ valuation q 72 = false := by
  rw [value15, value46, value51, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (24 : Vertex) (144 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 15 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value15, value51, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (24 : Vertex) (153 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 15 = false ∨ valuation q 52 = false ∨ valuation q 72 = false := by
  rw [value15, value51, value52, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (24 : Vertex) (153 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 15 = false ∨ valuation q 54 = false ∨ valuation q 72 = false := by
  rw [value15, value51, value54, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (24 : Vertex) (156 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 46 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value46, value51, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (144 : Vertex) (153 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 46 = false ∨ valuation q 52 = false ∨ valuation q 72 = false := by
  rw [value46, value51, value52, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (144 : Vertex) (153 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 46 = false ∨ valuation q 54 = false ∨ valuation q 72 = false := by
  rw [value46, value51, value54, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (144 : Vertex) (156 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 72 = false := by
  rw [value51, value52, value54, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (153 : Vertex) (156 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 167 = true ∨ valuation q 46 = true ∨ valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 72 = true := by
  rw [value46, value51, value52, value54, value72, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(144 : Vertex), (153 : Vertex), (156 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (24 : Vertex) [(144 : Vertex), (153 : Vertex), (156 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 167 = true ∨ valuation q 15 = true ∨ valuation q 46 = true ∨ valuation q 52 = true ∨ valuation q 72 = true := by
  rw [value15, value46, value51, value52, value72, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(24 : Vertex), (144 : Vertex), (153 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (156 : Vertex) [(24 : Vertex), (144 : Vertex), (153 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 53 = false := by
  rw [value47, value51, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (145 : Vertex) (152 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 73 = false := by
  rw [value47, value51, value52, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (145 : Vertex) (152 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 53 = false ∨ valuation q 73 = false := by
  rw [value47, value52, value53, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (145 : Vertex) (155 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value51, value52, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (152 : Vertex) (155 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 73 = false := by
  rw [value51, value52, value53, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (152 : Vertex) (155 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 73 = false := by
  rw [value51, value52, value55, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (152 : Vertex) (157 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 168 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 73 = true := by
  rw [value51, value52, value53, value55, value73, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(152 : Vertex), (155 : Vertex), (157 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (145 : Vertex) [(152 : Vertex), (155 : Vertex), (157 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 168 = true ∨ valuation q 47 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 73 = true := by
  rw [value47, value52, value53, value55, value73, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(145 : Vertex), (155 : Vertex), (157 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (152 : Vertex) [(145 : Vertex), (155 : Vertex), (157 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 168 = true ∨ valuation q 47 = true ∨ valuation q 51 = true ∨ valuation q 55 = true ∨ valuation q 73 = true := by
  rw [value47, value51, value52, value55, value73, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(145 : Vertex), (152 : Vertex), (157 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (155 : Vertex) [(145 : Vertex), (152 : Vertex), (157 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 168 = true ∨ valuation q 47 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 73 = true := by
  rw [value47, value51, value52, value53, value73, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (157 : Vertex) → w ∈ [(145 : Vertex), (152 : Vertex), (155 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (157 : Vertex) [(145 : Vertex), (152 : Vertex), (155 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 168 = true ∨ valuation q 47 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 55 = true := by
  rw [value47, value51, value52, value53, value55, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(145 : Vertex), (152 : Vertex), (155 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (185 : Vertex) [(145 : Vertex), (152 : Vertex), (155 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E257.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112257
