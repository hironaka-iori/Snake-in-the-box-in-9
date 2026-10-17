import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 168 = true ∨ valuation q 47 = true ∨ valuation q 49 = true ∨ valuation q 55 = true := by
  rw [value47, value48, value49, value55, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(180 : Vertex), (183 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (178 : Vertex) [(180 : Vertex), (183 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 168 = true ∨ valuation q 45 = true ∨ valuation q 49 = true ∨ valuation q 55 = true := by
  rw [value45, value48, value49, value55, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(178 : Vertex), (183 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (180 : Vertex) [(178 : Vertex), (183 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 168 = true ∨ valuation q 45 = true ∨ valuation q 47 = true ∨ valuation q 55 = true := by
  rw [value45, value47, value48, value55, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(178 : Vertex), (180 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (183 : Vertex) [(178 : Vertex), (180 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 168 = true ∨ valuation q 45 = true ∨ valuation q 47 = true ∨ valuation q 49 = true := by
  rw [value45, value47, value48, value49, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(178 : Vertex), (180 : Vertex), (183 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (190 : Vertex) [(178 : Vertex), (180 : Vertex), (183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 49 = true := by
  rw [value49, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (183 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 38 = false ∨ valuation q 46 = false := by
  rw [value12, value38, value46, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (167 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 38 = false ∨ valuation q 48 = false := by
  rw [value12, value38, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (167 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 38 = false ∨ valuation q 56 = false := by
  rw [value12, value38, value49, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (167 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 38 = false ∨ valuation q 70 = false := by
  rw [value12, value38, value49, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (167 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 38 = false ∨ valuation q 97 = false := by
  rw [value12, value38, value49, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (167 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value12, value46, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 46 = false ∨ valuation q 56 = false := by
  rw [value12, value46, value49, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (179 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 46 = false ∨ valuation q 70 = false := by
  rw [value12, value46, value49, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (179 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 46 = false ∨ valuation q 97 = false := by
  rw [value12, value46, value49, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (179 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 48 = false ∨ valuation q 56 = false := by
  rw [value12, value48, value49, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (182 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 48 = false ∨ valuation q 70 = false := by
  rw [value12, value48, value49, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (182 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 48 = false ∨ valuation q 97 = false := by
  rw [value12, value48, value49, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (182 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 56 = false ∨ valuation q 70 = false := by
  rw [value12, value49, value56, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (191 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 56 = false ∨ valuation q 97 = false := by
  rw [value12, value49, value56, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (191 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 12 = false ∨ valuation q 70 = false ∨ valuation q 97 = false := by
  rw [value12, value49, value70, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (55 : Vertex) (247 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 38 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value38, value46, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (167 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 38 = false ∨ valuation q 46 = false ∨ valuation q 56 = false := by
  rw [value38, value46, value49, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (167 : Vertex) (179 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 38 = false ∨ valuation q 46 = false ∨ valuation q 70 = false := by
  rw [value38, value46, value49, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (167 : Vertex) (179 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 38 = false ∨ valuation q 46 = false ∨ valuation q 97 = false := by
  rw [value38, value46, value49, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (167 : Vertex) (179 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 38 = false ∨ valuation q 48 = false ∨ valuation q 56 = false := by
  rw [value38, value48, value49, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (167 : Vertex) (182 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 38 = false ∨ valuation q 48 = false ∨ valuation q 70 = false := by
  rw [value38, value48, value49, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (167 : Vertex) (182 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 38 = false ∨ valuation q 48 = false ∨ valuation q 97 = false := by
  rw [value38, value48, value49, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (167 : Vertex) (182 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 38 = false ∨ valuation q 56 = false ∨ valuation q 70 = false := by
  rw [value38, value49, value56, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (167 : Vertex) (191 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 38 = false ∨ valuation q 56 = false ∨ valuation q 97 = false := by
  rw [value38, value49, value56, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (167 : Vertex) (191 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 38 = false ∨ valuation q 70 = false ∨ valuation q 97 = false := by
  rw [value38, value49, value70, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (167 : Vertex) (247 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 56 = false := by
  rw [value46, value48, value49, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (179 : Vertex) (182 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 70 = false := by
  rw [value46, value48, value49, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (179 : Vertex) (182 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E004.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112004
