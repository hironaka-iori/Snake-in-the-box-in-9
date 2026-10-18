import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 157 = true ∨ valuation q 12 = true ∨ valuation q 31 = true ∨ valuation q 66 = true := by
  rw [value12, value30, value31, value66, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (116 : Vertex) w → w ∈ region → w ≠ (112 : Vertex) → w ∈ [(84 : Vertex), (118 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (116 : Vertex) (112 : Vertex) [(84 : Vertex), (118 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 157 = true ∨ valuation q 12 = true ∨ valuation q 27 = true ∨ valuation q 66 = true := by
  rw [value12, value27, value30, value66, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (116 : Vertex) w → w ∈ region → w ≠ (118 : Vertex) → w ∈ [(84 : Vertex), (112 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (116 : Vertex) (118 : Vertex) [(84 : Vertex), (112 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 157 = true ∨ valuation q 12 = true ∨ valuation q 27 = true ∨ valuation q 31 = true := by
  rw [value12, value27, value30, value31, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (116 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(84 : Vertex), (112 : Vertex), (118 : Vertex)] := by decide
  have hg := other_cover q (116 : Vertex) (244 : Vertex) [(84 : Vertex), (112 : Vertex), (118 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 30 = false ∨ valuation q 34 = false ∨ valuation q 68 = false := by
  rw [value30, value31, value34, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (118 : Vertex) (116 : Vertex) (126 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 158 = true ∨ valuation q 34 = true ∨ valuation q 68 = true := by
  rw [value31, value34, value68, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (116 : Vertex) → w ∈ [(126 : Vertex), (246 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (116 : Vertex) [(126 : Vertex), (246 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 158 = true ∨ valuation q 30 = true ∨ valuation q 34 = true := by
  rw [value30, value31, value34, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(116 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (246 : Vertex) [(116 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 15 = false ∨ valuation q 34 = false ∨ valuation q 70 = false := by
  rw [value15, value32, value34, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (122 : Vertex) (90 : Vertex) (126 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 159 = true ∨ valuation q 34 = true ∨ valuation q 70 = true := by
  rw [value32, value34, value70, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(126 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (90 : Vertex) [(126 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 159 = true ∨ valuation q 15 = true ∨ valuation q 34 = true := by
  rw [value15, value32, value34, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(90 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (250 : Vertex) [(90 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 160 = true ∨ valuation q 35 = true ∨ valuation q 72 = true ∨ valuation q 99 = true := by
  rw [value33, value35, value72, value99, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (93 : Vertex) → w ∈ [(127 : Vertex), (253 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (93 : Vertex) [(127 : Vertex), (253 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 160 = true ∨ valuation q 16 = true ∨ valuation q 72 = true ∨ valuation q 99 = true := by
  rw [value16, value33, value72, value99, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (127 : Vertex) → w ∈ [(93 : Vertex), (253 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (127 : Vertex) [(93 : Vertex), (253 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 160 = true ∨ valuation q 16 = true ∨ valuation q 35 = true ∨ valuation q 99 = true := by
  rw [value16, value33, value35, value99, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (253 : Vertex) → w ∈ [(93 : Vertex), (127 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (253 : Vertex) [(93 : Vertex), (127 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 160 = true ∨ valuation q 16 = true ∨ valuation q 35 = true ∨ valuation q 72 = true := by
  rw [value16, value33, value35, value72, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (381 : Vertex) → w ∈ [(93 : Vertex), (127 : Vertex), (253 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (381 : Vertex) [(93 : Vertex), (127 : Vertex), (253 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 34 = true := by
  rw [value34, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (126 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 17 = false ∨ valuation q 26 = false ∨ valuation q 31 = false := by
  rw [value17, value26, value31, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (94 : Vertex) (110 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 17 = false ∨ valuation q 26 = false ∨ valuation q 32 = false := by
  rw [value17, value26, value32, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (94 : Vertex) (110 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 17 = false ∨ valuation q 26 = false ∨ valuation q 35 = false := by
  rw [value17, value26, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (94 : Vertex) (110 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 17 = false ∨ valuation q 26 = false ∨ valuation q 73 = false := by
  rw [value17, value26, value34, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (94 : Vertex) (110 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 17 = false ∨ valuation q 31 = false ∨ valuation q 32 = false := by
  rw [value17, value31, value32, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (94 : Vertex) (118 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 17 = false ∨ valuation q 31 = false ∨ valuation q 73 = false := by
  rw [value17, value31, value34, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (94 : Vertex) (118 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 26 = false ∨ valuation q 31 = false ∨ valuation q 32 = false := by
  rw [value26, value31, value32, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (110 : Vertex) (118 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 26 = false ∨ valuation q 31 = false ∨ valuation q 35 = false := by
  rw [value26, value31, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (110 : Vertex) (118 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 26 = false ∨ valuation q 31 = false ∨ valuation q 73 = false := by
  rw [value26, value31, value34, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (110 : Vertex) (118 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 26 = false ∨ valuation q 32 = false ∨ valuation q 35 = false := by
  rw [value26, value32, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (110 : Vertex) (122 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 26 = false ∨ valuation q 32 = false ∨ valuation q 73 = false := by
  rw [value26, value32, value34, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (110 : Vertex) (122 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 73 = false := by
  rw [value31, value32, value34, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (118 : Vertex) (122 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 18 = false ∨ valuation q 33 = false ∨ valuation q 34 = false := by
  rw [value18, value33, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (127 : Vertex) (95 : Vertex) (125 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 101 = false := by
  rw [value33, value34, value35, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (127 : Vertex) (125 : Vertex) (126 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 162 = true ∨ valuation q 18 = true ∨ valuation q 34 = true ∨ valuation q 101 = true := by
  rw [value18, value34, value35, value101, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (127 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(95 : Vertex), (126 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (127 : Vertex) (125 : Vertex) [(95 : Vertex), (126 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 36 = true := by
  rw [value36, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (192 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 39 = true ∨ valuation q 40 = true ∨ valuation q 55 = true := by
  rw [value36, value37, value38, value39, value40, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ∈ [(193 : Vertex), (194 : Vertex), (196 : Vertex), (200 : Vertex), (224 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (192 : Vertex) [(193 : Vertex), (194 : Vertex), (196 : Vertex), (200 : Vertex), (224 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value36, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (194 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E256.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112256
