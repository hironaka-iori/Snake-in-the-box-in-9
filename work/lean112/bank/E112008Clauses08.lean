import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 165 = true ∨ valuation q 38 = true ∨ valuation q 42 = true ∨ valuation q 94 = true := by
  rw [value38, value41, value42, value94, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (164 : Vertex) → w ∈ [(168 : Vertex), (174 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (164 : Vertex) [(168 : Vertex), (174 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 165 = true ∨ valuation q 35 = true ∨ valuation q 42 = true ∨ valuation q 94 = true := by
  rw [value35, value41, value42, value94, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(164 : Vertex), (174 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (168 : Vertex) [(164 : Vertex), (174 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 165 = true ∨ valuation q 35 = true ∨ valuation q 38 = true ∨ valuation q 94 = true := by
  rw [value35, value38, value41, value94, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(164 : Vertex), (168 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (174 : Vertex) [(164 : Vertex), (168 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 165 = true ∨ valuation q 35 = true ∨ valuation q 38 = true ∨ valuation q 42 = true := by
  rw [value35, value38, value41, value42, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(164 : Vertex), (168 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (428 : Vertex) [(164 : Vertex), (168 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 96 = false := by
  rw [value37, value39, value42, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (166 : Vertex) (170 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 37 = false ∨ valuation q 41 = false ∨ valuation q 96 = false := by
  rw [value37, value41, value42, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (166 : Vertex) (172 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 96 = false := by
  rw [value39, value41, value42, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (170 : Vertex) (172 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 166 = true ∨ valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 96 = true := by
  rw [value39, value41, value42, value96, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (174 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(170 : Vertex), (172 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (174 : Vertex) (166 : Vertex) [(170 : Vertex), (172 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 166 = true ∨ valuation q 37 = true ∨ valuation q 41 = true ∨ valuation q 96 = true := by
  rw [value37, value41, value42, value96, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (174 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(166 : Vertex), (172 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (174 : Vertex) (170 : Vertex) [(166 : Vertex), (172 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 166 = true ∨ valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 96 = true := by
  rw [value37, value39, value42, value96, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (174 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(166 : Vertex), (170 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (174 : Vertex) (172 : Vertex) [(166 : Vertex), (170 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 166 = true ∨ valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 41 = true := by
  rw [value37, value39, value41, value42, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (174 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(166 : Vertex), (170 : Vertex), (172 : Vertex)] := by decide
  have hg := other_cover q (174 : Vertex) (430 : Vertex) [(166 : Vertex), (170 : Vertex), (172 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 34 = false ∨ valuation q 45 = false ∨ valuation q 63 = false := by
  rw [value34, value43, value45, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (182 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 34 = false ∨ valuation q 45 = false ∨ valuation q 100 = false := by
  rw [value34, value43, value45, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (182 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 63 = false ∨ valuation q 100 = false := by
  rw [value43, value45, value63, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (182 : Vertex) (242 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 167 = true ∨ valuation q 34 = true ∨ valuation q 63 = true ∨ valuation q 100 = true := by
  rw [value34, value43, value63, value100, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (178 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(162 : Vertex), (242 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (178 : Vertex) (182 : Vertex) [(162 : Vertex), (242 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 36 = false ∨ valuation q 46 = false ∨ valuation q 50 = false := by
  rw [value36, value44, value46, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (181 : Vertex) (165 : Vertex) (183 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 168 = true ∨ valuation q 46 = true ∨ valuation q 50 = true := by
  rw [value44, value46, value50, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(183 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (165 : Vertex) [(183 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 168 = true ∨ valuation q 36 = true ∨ valuation q 50 = true := by
  rw [value36, value44, value50, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(165 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (183 : Vertex) [(165 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 168 = true ∨ valuation q 36 = true ∨ valuation q 46 = true := by
  rw [value36, value44, value46, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(165 : Vertex), (183 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (189 : Vertex) [(165 : Vertex), (183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 37 = false ∨ valuation q 43 = false ∨ valuation q 46 = false := by
  rw [value37, value43, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (182 : Vertex) (166 : Vertex) (178 : Vertex) (183 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 169 = true ∨ valuation q 43 = true ∨ valuation q 46 = true := by
  rw [value43, value45, value46, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(178 : Vertex), (183 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (166 : Vertex) [(178 : Vertex), (183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 169 = true ∨ valuation q 37 = true ∨ valuation q 46 = true := by
  rw [value37, value45, value46, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(166 : Vertex), (183 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (178 : Vertex) [(166 : Vertex), (183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 169 = true ∨ valuation q 37 = true ∨ valuation q 43 = true := by
  rw [value37, value43, value45, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(166 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (183 : Vertex) [(166 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 13 = false ∨ valuation q 44 = false ∨ valuation q 45 = false := by
  rw [value13, value44, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (181 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 13 = false ∨ valuation q 44 = false ∨ valuation q 51 = false := by
  rw [value13, value44, value46, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (181 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 13 = false ∨ valuation q 45 = false ∨ valuation q 51 = false := by
  rw [value13, value45, value46, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (182 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 51 = false := by
  rw [value44, value45, value46, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (181 : Vertex) (182 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 170 = true ∨ valuation q 13 = true ∨ valuation q 45 = true ∨ valuation q 51 = true := by
  rw [value13, value45, value46, value51, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(55 : Vertex), (182 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (181 : Vertex) [(55 : Vertex), (182 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 170 = true ∨ valuation q 13 = true ∨ valuation q 44 = true ∨ valuation q 51 = true := by
  rw [value13, value44, value46, value51, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(55 : Vertex), (181 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (182 : Vertex) [(55 : Vertex), (181 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 14 = false ∨ valuation q 38 = false ∨ valuation q 48 = false := by
  rw [value14, value38, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (168 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 14 = false ∨ valuation q 38 = false ∨ valuation q 66 = false := by
  rw [value14, value38, value47, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (168 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 14 = false ∨ valuation q 38 = false ∨ valuation q 103 = false := by
  rw [value14, value38, value47, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (168 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E008.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112008
