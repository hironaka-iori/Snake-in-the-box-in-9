import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 160 = true ∨ valuation q 6 = true ∨ valuation q 44 = true ∨ valuation q 45 = true := by
  rw [value6, value43, value44, value45, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (136 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(8 : Vertex), (137 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (136 : Vertex) (152 : Vertex) [(8 : Vertex), (137 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 39 = false ∨ valuation q 43 = false := by
  rw [value7, value39, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (9 : Vertex) (129 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 39 = false ∨ valuation q 61 = false := by
  rw [value7, value39, value44, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (9 : Vertex) (129 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 43 = false ∨ valuation q 61 = false := by
  rw [value7, value43, value44, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (9 : Vertex) (136 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 39 = false ∨ valuation q 43 = false ∨ valuation q 61 = false := by
  rw [value39, value43, value44, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (129 : Vertex) (136 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 161 = true ∨ valuation q 7 = true ∨ valuation q 39 = true ∨ valuation q 61 = true := by
  rw [value7, value39, value44, value61, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(9 : Vertex), (129 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (136 : Vertex) [(9 : Vertex), (129 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 43 = false ∨ valuation q 46 = false ∨ valuation q 52 = false := by
  rw [value43, value45, value46, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (136 : Vertex) (142 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 162 = true ∨ valuation q 43 = true ∨ valuation q 52 = true := by
  rw [value43, value45, value52, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(136 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (142 : Vertex) [(136 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 163 = true ∨ valuation q 45 = true ∨ valuation q 64 = true := by
  rw [value45, value46, value64, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(138 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (134 : Vertex) [(138 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 163 = true ∨ valuation q 42 = true ∨ valuation q 64 = true := by
  rw [value42, value46, value64, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(134 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (138 : Vertex) [(134 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 14 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value14, value47, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (147 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 14 = false ∨ valuation q 48 = false ∨ valuation q 68 = false := by
  rw [value14, value47, value48, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (147 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 68 = false := by
  rw [value47, value48, value52, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (147 : Vertex) (154 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 164 = true ∨ valuation q 14 = true ∨ valuation q 52 = true ∨ valuation q 68 = true := by
  rw [value14, value47, value52, value68, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(18 : Vertex), (154 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (147 : Vertex) [(18 : Vertex), (154 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 15 = false ∨ valuation q 47 = false ∨ valuation q 53 = false := by
  rw [value15, value47, value48, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (19 : Vertex) (146 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 165 = true ∨ valuation q 47 = true ∨ valuation q 53 = true ∨ valuation q 69 = true := by
  rw [value47, value48, value53, value69, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(146 : Vertex), (155 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (19 : Vertex) [(146 : Vertex), (155 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 165 = true ∨ valuation q 15 = true ∨ valuation q 53 = true ∨ valuation q 69 = true := by
  rw [value15, value48, value53, value69, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(19 : Vertex), (155 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (146 : Vertex) [(19 : Vertex), (155 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 165 = true ∨ valuation q 15 = true ∨ valuation q 47 = true ∨ valuation q 69 = true := by
  rw [value15, value47, value48, value69, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(19 : Vertex), (146 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (155 : Vertex) [(19 : Vertex), (146 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 165 = true ∨ valuation q 15 = true ∨ valuation q 47 = true ∨ valuation q 53 = true := by
  rw [value15, value47, value48, value53, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(19 : Vertex), (146 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (211 : Vertex) [(19 : Vertex), (146 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 16 = false ∨ valuation q 40 = false ∨ valuation q 50 = false := by
  rw [value16, value40, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (20 : Vertex) (132 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 16 = false ∨ valuation q 40 = false ∨ valuation q 70 = false := by
  rw [value16, value40, value49, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (20 : Vertex) (132 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 16 = false ∨ valuation q 50 = false ∨ valuation q 70 = false := by
  rw [value16, value49, value50, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (20 : Vertex) (149 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 40 = false ∨ valuation q 50 = false ∨ valuation q 70 = false := by
  rw [value40, value49, value50, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (132 : Vertex) (149 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 167 = true ∨ valuation q 49 = true ∨ valuation q 54 = true := by
  rw [value49, value50, value54, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(148 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (133 : Vertex) [(148 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 167 = true ∨ valuation q 41 = true ∨ valuation q 54 = true := by
  rw [value41, value50, value54, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(133 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (148 : Vertex) [(133 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 167 = true ∨ valuation q 41 = true ∨ valuation q 49 = true := by
  rw [value41, value49, value50, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (157 : Vertex) → w ∈ [(133 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (157 : Vertex) [(133 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 18 = false ∨ valuation q 43 = false ∨ valuation q 52 = false := by
  rw [value18, value43, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (24 : Vertex) (136 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 71 = false := by
  rw [value45, value47, value52, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (146 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 53 = false ∨ valuation q 71 = false := by
  rw [value45, value52, value53, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (155 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 169 = true ∨ valuation q 45 = true ∨ valuation q 47 = true ∨ valuation q 51 = true ∨ valuation q 53 = true := by
  rw [value45, value47, value51, value52, value53, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (154 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(138 : Vertex), (146 : Vertex), (152 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (154 : Vertex) (218 : Vertex) [(138 : Vertex), (146 : Vertex), (152 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 19 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value19, value48, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (27 : Vertex) (147 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 19 = false ∨ valuation q 48 = false ∨ valuation q 55 = false := by
  rw [value19, value48, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (27 : Vertex) (147 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E115.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112115
