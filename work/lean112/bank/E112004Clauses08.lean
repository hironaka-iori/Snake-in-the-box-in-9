import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 9 = false ∨ valuation q 45 = false ∨ valuation q 47 = false := by
  rw [value9, value44, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (178 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 9 = false ∨ valuation q 45 = false ∨ valuation q 66 = false := by
  rw [value9, value44, value45, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (178 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 9 = false ∨ valuation q 45 = false ∨ valuation q 94 = false := by
  rw [value9, value44, value45, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (178 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 9 = false ∨ valuation q 47 = false ∨ valuation q 66 = false := by
  rw [value9, value44, value47, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (180 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 9 = false ∨ valuation q 47 = false ∨ valuation q 94 = false := by
  rw [value9, value44, value47, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (180 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 9 = false ∨ valuation q 66 = false ∨ valuation q 94 = false := by
  rw [value9, value44, value66, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (240 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 34 = false ∨ valuation q 45 = false ∨ valuation q 47 = false := by
  rw [value34, value44, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (178 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 34 = false ∨ valuation q 45 = false ∨ valuation q 50 = false := by
  rw [value34, value44, value45, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (178 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 34 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value34, value44, value47, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (180 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 34 = false ∨ valuation q 47 = false ∨ valuation q 66 = false := by
  rw [value34, value44, value47, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (180 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 66 = false := by
  rw [value44, value45, value47, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (178 : Vertex) (180 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 36 = false ∨ valuation q 44 = false ∨ valuation q 46 = false := by
  rw [value36, value44, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (176 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 36 = false ∨ valuation q 44 = false ∨ valuation q 48 = false := by
  rw [value36, value44, value45, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (176 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 36 = false ∨ valuation q 44 = false ∨ valuation q 52 = false := by
  rw [value36, value44, value45, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (176 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 36 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value36, value45, value46, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 36 = false ∨ valuation q 46 = false ∨ valuation q 52 = false := by
  rw [value36, value45, value46, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (179 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 36 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value36, value45, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (182 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value44, value45, value46, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (176 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 52 = false := by
  rw [value44, value45, value46, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (176 : Vertex) (179 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value44, value45, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (176 : Vertex) (182 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value45, value46, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (179 : Vertex) (182 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 10 = false ∨ valuation q 37 = false ∨ valuation q 45 = false := by
  rw [value10, value37, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (51 : Vertex) (163 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 10 = false ∨ valuation q 37 = false ∨ valuation q 95 = false := by
  rw [value10, value37, value46, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (51 : Vertex) (163 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 10 = false ∨ valuation q 45 = false ∨ valuation q 95 = false := by
  rw [value10, value45, value46, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (51 : Vertex) (178 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 37 = false ∨ valuation q 45 = false ∨ valuation q 95 = false := by
  rw [value37, value45, value46, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (163 : Vertex) (178 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 166 = true ∨ valuation q 37 = true ∨ valuation q 45 = true ∨ valuation q 49 = true ∨ valuation q 68 = true ∨ valuation q 95 = true := by
  rw [value37, value45, value46, value49, value68, value95, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (51 : Vertex) → w ∈ [(163 : Vertex), (178 : Vertex), (183 : Vertex), (243 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (51 : Vertex) [(163 : Vertex), (178 : Vertex), (183 : Vertex), (243 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 166 = true ∨ valuation q 10 = true ∨ valuation q 45 = true ∨ valuation q 49 = true ∨ valuation q 68 = true ∨ valuation q 95 = true := by
  rw [value10, value45, value46, value49, value68, value95, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(51 : Vertex), (178 : Vertex), (183 : Vertex), (243 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (163 : Vertex) [(51 : Vertex), (178 : Vertex), (183 : Vertex), (243 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 166 = true ∨ valuation q 10 = true ∨ valuation q 37 = true ∨ valuation q 45 = true ∨ valuation q 49 = true ∨ valuation q 68 = true := by
  rw [value10, value37, value45, value46, value49, value68, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(51 : Vertex), (163 : Vertex), (178 : Vertex), (183 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (435 : Vertex) [(51 : Vertex), (163 : Vertex), (178 : Vertex), (183 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 47 = true := by
  rw [value47, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (180 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 44 = true ∨ valuation q 48 = true ∨ valuation q 53 = true := by
  rw [value44, value47, value48, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (180 : Vertex) w → w ∈ region → w ∈ [(176 : Vertex), (182 : Vertex), (188 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (180 : Vertex) [(176 : Vertex), (182 : Vertex), (188 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 44 = false ∨ valuation q 48 = false ∨ valuation q 53 = false := by
  rw [value44, value47, value48, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (176 : Vertex) (182 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 167 = true ∨ valuation q 44 = true ∨ valuation q 53 = true := by
  rw [value44, value47, value53, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (180 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(176 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (180 : Vertex) (182 : Vertex) [(176 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E004.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112004
