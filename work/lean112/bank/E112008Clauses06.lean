import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 159 = true ∨ valuation q 32 = true ∨ valuation q 36 = true ∨ valuation q 41 = true := by
  rw [value32, value35, value36, value41, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(160 : Vertex), (165 : Vertex), (172 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (166 : Vertex) [(160 : Vertex), (165 : Vertex), (172 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 159 = true ∨ valuation q 32 = true ∨ valuation q 36 = true ∨ valuation q 37 = true := by
  rw [value32, value35, value36, value37, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(160 : Vertex), (165 : Vertex), (166 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (172 : Vertex) [(160 : Vertex), (165 : Vertex), (166 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 44 = false := by
  rw [value33, value35, value36, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (164 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 54 = false := by
  rw [value33, value35, value36, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (164 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 90 = false := by
  rw [value33, value35, value36, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (164 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 33 = false ∨ valuation q 44 = false ∨ valuation q 54 = false := by
  rw [value33, value36, value44, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (181 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 33 = false ∨ valuation q 44 = false ∨ valuation q 90 = false := by
  rw [value33, value36, value44, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (181 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 33 = false ∨ valuation q 54 = false ∨ valuation q 90 = false := by
  rw [value33, value36, value54, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (229 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 35 = false ∨ valuation q 44 = false ∨ valuation q 54 = false := by
  rw [value35, value36, value44, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (164 : Vertex) (181 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 35 = false ∨ valuation q 44 = false ∨ valuation q 90 = false := by
  rw [value35, value36, value44, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (164 : Vertex) (181 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 35 = false ∨ valuation q 54 = false ∨ valuation q 90 = false := by
  rw [value35, value36, value54, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (164 : Vertex) (229 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 44 = false ∨ valuation q 54 = false ∨ valuation q 90 = false := by
  rw [value36, value44, value54, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (181 : Vertex) (229 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 44 = false ∨ valuation q 90 = false := by
  rw [value44, value90, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (165 : Vertex) (181 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 160 = true ∨ valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 54 = true ∨ valuation q 90 = true := by
  rw [value33, value35, value36, value54, value90, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (165 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(161 : Vertex), (164 : Vertex), (229 : Vertex), (421 : Vertex)] := by decide
  have hg := other_cover q (165 : Vertex) (181 : Vertex) [(161 : Vertex), (164 : Vertex), (229 : Vertex), (421 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 160 = true ∨ valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 44 = true ∨ valuation q 54 = true := by
  rw [value33, value35, value36, value44, value54, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (165 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(161 : Vertex), (164 : Vertex), (181 : Vertex), (229 : Vertex)] := by decide
  have hg := other_cover q (165 : Vertex) (421 : Vertex) [(161 : Vertex), (164 : Vertex), (181 : Vertex), (229 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 42 = false := by
  rw [value34, value35, value37, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (164 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 45 = false := by
  rw [value34, value35, value37, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (164 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 34 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value34, value37, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (174 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value35, value37, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (164 : Vertex) (174 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 161 = true ∨ valuation q 34 = true ∨ valuation q 35 = true ∨ valuation q 45 = true := by
  rw [value34, value35, value37, value45, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(162 : Vertex), (164 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (174 : Vertex) [(162 : Vertex), (164 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 161 = true ∨ valuation q 34 = true ∨ valuation q 35 = true ∨ valuation q 42 = true := by
  rw [value34, value35, value37, value42, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(162 : Vertex), (164 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (182 : Vertex) [(162 : Vertex), (164 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 47 = false := by
  rw [value32, value38, value39, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (170 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 41 = false ∨ valuation q 47 = false := by
  rw [value32, value38, value41, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (172 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 41 = false ∨ valuation q 92 = false := by
  rw [value32, value38, value41, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (172 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 47 = false := by
  rw [value38, value39, value41, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (170 : Vertex) (172 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 92 = false := by
  rw [value38, value39, value41, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (170 : Vertex) (172 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 162 = true ∨ valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 47 = true ∨ valuation q 92 = true := by
  rw [value38, value39, value41, value47, value92, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(170 : Vertex), (172 : Vertex), (184 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (160 : Vertex) [(170 : Vertex), (172 : Vertex), (184 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 162 = true ∨ valuation q 32 = true ∨ valuation q 41 = true ∨ valuation q 47 = true ∨ valuation q 92 = true := by
  rw [value32, value38, value41, value47, value92, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(160 : Vertex), (172 : Vertex), (184 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (170 : Vertex) [(160 : Vertex), (172 : Vertex), (184 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 162 = true ∨ valuation q 32 = true ∨ valuation q 39 = true ∨ valuation q 47 = true ∨ valuation q 92 = true := by
  rw [value32, value38, value39, value47, value92, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(160 : Vertex), (170 : Vertex), (184 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (172 : Vertex) [(160 : Vertex), (170 : Vertex), (184 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 162 = true ∨ valuation q 32 = true ∨ valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 92 = true := by
  rw [value32, value38, value39, value41, value92, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(160 : Vertex), (170 : Vertex), (172 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (184 : Vertex) [(160 : Vertex), (170 : Vertex), (172 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 162 = true ∨ valuation q 32 = true ∨ valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 47 = true := by
  rw [value32, value38, value39, value41, value47, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(160 : Vertex), (170 : Vertex), (172 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (424 : Vertex) [(160 : Vertex), (170 : Vertex), (172 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 6 = false ∨ valuation q 34 = false ∨ valuation q 38 = false := by
  rw [value6, value34, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (42 : Vertex) (162 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E008.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112008
