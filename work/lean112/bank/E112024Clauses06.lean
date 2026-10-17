import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 19 = false ∨ valuation q 37 = false ∨ valuation q 47 = false := by
  rw [value19, value37, value38, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (234 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 19 = false ∨ valuation q 37 = false ∨ valuation q 110 = false := by
  rw [value19, value37, value38, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (234 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 19 = false ∨ valuation q 47 = false ∨ valuation q 110 = false := by
  rw [value19, value38, value47, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (251 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 47 = false := by
  rw [value33, value37, value38, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (234 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 160 = true ∨ valuation q 40 = true := by
  rw [value39, value40, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(238 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (228 : Vertex) [(238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 160 = true ∨ valuation q 34 = true := by
  rw [value34, value39, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(228 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (238 : Vertex) [(228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 40 = true := by
  rw [value40, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (238 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 36 = true ∨ valuation q 37 = true ∨ valuation q 39 = true := by
  rw [value36, value37, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ∈ [(230 : Vertex), (234 : Vertex), (236 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (238 : Vertex) [(230 : Vertex), (234 : Vertex), (236 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 39 = false := by
  rw [value36, value37, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (238 : Vertex) (230 : Vertex) (234 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value36, value37, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (238 : Vertex) (230 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 37 = false ∨ valuation q 39 = false := by
  rw [value37, value39, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (238 : Vertex) (234 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 161 = true ∨ valuation q 37 = true ∨ valuation q 39 = true := by
  rw [value37, value39, value40, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [(234 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (230 : Vertex) [(234 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 161 = true ∨ valuation q 36 = true ∨ valuation q 39 = true := by
  rw [value36, value39, value40, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (234 : Vertex) → w ∈ [(230 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (234 : Vertex) [(230 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 161 = true ∨ valuation q 36 = true ∨ valuation q 37 = true := by
  rw [value36, value37, value40, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(230 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (236 : Vertex) [(230 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 34 = false ∨ valuation q 42 = false ∨ valuation q 116 = false := by
  rw [value34, value41, value42, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (228 : Vertex) (245 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 162 = true ∨ valuation q 34 = true ∨ valuation q 116 = true := by
  rw [value34, value41, value116, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(228 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (245 : Vertex) [(228 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 162 = true ∨ valuation q 34 = true ∨ valuation q 42 = true := by
  rw [value34, value41, value42, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(228 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (500 : Vertex) [(228 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value35, value41, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (229 : Vertex) (244 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 164 = true ∨ valuation q 48 = true := by
  rw [value43, value48, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (245 : Vertex) [(255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 164 = true ∨ valuation q 42 = true := by
  rw [value42, value43, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(245 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (255 : Vertex) [(245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 165 = true ∨ valuation q 45 = true ∨ valuation q 46 = true := by
  rw [value44, value45, value46, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(249 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (184 : Vertex) [(249 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 165 = true ∨ valuation q 27 = true ∨ valuation q 46 = true := by
  rw [value27, value44, value46, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(184 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (249 : Vertex) [(184 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 165 = true ∨ valuation q 27 = true ∨ valuation q 45 = true := by
  rw [value27, value44, value45, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(184 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (250 : Vertex) [(184 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 166 = true ∨ valuation q 47 = true := by
  rw [value45, value47, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(251 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (248 : Vertex) [(251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 166 = true ∨ valuation q 44 = true := by
  rw [value44, value45, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(248 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (251 : Vertex) [(248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 37 = false ∨ valuation q 44 = false ∨ valuation q 47 = false := by
  rw [value37, value44, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 37 = false ∨ valuation q 44 = false ∨ valuation q 118 = false := by
  rw [value37, value44, value46, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (248 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 37 = false ∨ valuation q 47 = false ∨ valuation q 118 = false := by
  rw [value37, value46, value47, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (251 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 118 = false := by
  rw [value44, value46, value47, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (248 : Vertex) (251 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 38 = false ∨ valuation q 45 = false ∨ valuation q 48 = false := by
  rw [value38, value45, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (249 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 38 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value38, value46, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (250 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value45, value46, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (249 : Vertex) (250 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E024.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112024
