import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 16 = false ∨ valuation q 42 = false ∨ valuation q 48 = false := by
  rw [value16, value42, value48, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (27 : Vertex) (139 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 16 = false ∨ valuation q 42 = false ∨ valuation q 52 = false := by
  rw [value16, value42, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (27 : Vertex) (139 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 16 = false ∨ valuation q 42 = false ∨ valuation q 75 = false := by
  rw [value16, value42, value53, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (27 : Vertex) (139 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 16 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value16, value48, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (27 : Vertex) (147 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 16 = false ∨ valuation q 48 = false ∨ valuation q 75 = false := by
  rw [value16, value48, value53, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (27 : Vertex) (147 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 16 = false ∨ valuation q 52 = false ∨ valuation q 75 = false := by
  rw [value16, value52, value53, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (27 : Vertex) (153 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 42 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value42, value48, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (139 : Vertex) (147 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 42 = false ∨ valuation q 48 = false ∨ valuation q 75 = false := by
  rw [value42, value48, value53, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (139 : Vertex) (147 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 42 = false ∨ valuation q 52 = false ∨ valuation q 75 = false := by
  rw [value42, value52, value53, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (139 : Vertex) (153 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 75 = false := by
  rw [value48, value52, value53, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (147 : Vertex) (153 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 169 = true ∨ valuation q 42 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 75 = true := by
  rw [value42, value48, value52, value53, value75, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(139 : Vertex), (147 : Vertex), (153 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (27 : Vertex) [(139 : Vertex), (147 : Vertex), (153 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 17 = false ∨ valuation q 43 = false ∨ valuation q 51 = false := by
  rw [value17, value43, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (28 : Vertex) (140 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 17 = false ∨ valuation q 43 = false ∨ valuation q 56 = false := by
  rw [value17, value43, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (28 : Vertex) (140 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 17 = false ∨ valuation q 51 = false ∨ valuation q 56 = false := by
  rw [value17, value51, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (28 : Vertex) (152 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 17 = false ∨ valuation q 55 = false ∨ valuation q 76 = false := by
  rw [value17, value54, value55, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (28 : Vertex) (157 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 17 = false ∨ valuation q 56 = false ∨ valuation q 76 = false := by
  rw [value17, value54, value56, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (28 : Vertex) (158 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 43 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value43, value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (140 : Vertex) (157 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 76 = false := by
  rw [value51, value54, value56, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (152 : Vertex) (158 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 170 = true ∨ valuation q 43 = true ∨ valuation q 51 = true ∨ valuation q 55 = true ∨ valuation q 56 = true ∨ valuation q 76 = true := by
  rw [value43, value51, value54, value55, value56, value76, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(140 : Vertex), (152 : Vertex), (157 : Vertex), (158 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (28 : Vertex) [(140 : Vertex), (152 : Vertex), (157 : Vertex), (158 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 170 = true ∨ valuation q 17 = true ∨ valuation q 43 = true ∨ valuation q 51 = true ∨ valuation q 55 = true ∨ valuation q 56 = true := by
  rw [value17, value43, value51, value54, value55, value56, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(28 : Vertex), (140 : Vertex), (152 : Vertex), (157 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (188 : Vertex) [(28 : Vertex), (140 : Vertex), (152 : Vertex), (157 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 44 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value44, value49, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (141 : Vertex) (149 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 44 = false ∨ valuation q 49 = false ∨ valuation q 54 = false := by
  rw [value44, value49, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (141 : Vertex) (149 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 44 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value44, value52, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (141 : Vertex) (153 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value49, value52, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (149 : Vertex) (153 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 171 = true ∨ valuation q 44 = true ∨ valuation q 52 = true ∨ valuation q 54 = true := by
  rw [value44, value52, value54, value55, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (157 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(141 : Vertex), (153 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (157 : Vertex) (149 : Vertex) [(141 : Vertex), (153 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 45 = false ∨ valuation q 50 = false ∨ valuation q 54 = false := by
  rw [value45, value50, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (142 : Vertex) (150 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 172 = true ∨ valuation q 45 = true ∨ valuation q 54 = true := by
  rw [value45, value54, value56, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(142 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (150 : Vertex) [(142 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 19 = false ∨ valuation q 59 = false ∨ valuation q 62 = false := by
  rw [value19, value57, value59, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (165 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 173 = true ∨ valuation q 59 = true ∨ valuation q 62 = true := by
  rw [value57, value59, value62, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(165 : Vertex), (169 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (33 : Vertex) [(165 : Vertex), (169 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 173 = true ∨ valuation q 19 = true ∨ valuation q 62 = true := by
  rw [value19, value57, value62, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(33 : Vertex), (169 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (165 : Vertex) [(33 : Vertex), (169 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 173 = true ∨ valuation q 19 = true ∨ valuation q 59 = true := by
  rw [value19, value57, value59, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(33 : Vertex), (165 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (169 : Vertex) [(33 : Vertex), (165 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 63 = false ∨ valuation q 68 = false := by
  rw [value58, value60, value63, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (166 : Vertex) (170 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E257.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112257
