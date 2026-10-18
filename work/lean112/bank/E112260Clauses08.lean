import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 2 = false ∨ valuation q 42 = false ∨ valuation q 56 = false := by
  rw [value2, value38, value42, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (202 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 2 = false ∨ valuation q 49 = false ∨ valuation q 56 = false := by
  rw [value2, value38, value49, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (210 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 36 = false ∨ valuation q 42 = false ∨ valuation q 49 = false := by
  rw [value36, value38, value42, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (192 : Vertex) (202 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 36 = false ∨ valuation q 42 = false ∨ valuation q 56 = false := by
  rw [value36, value38, value42, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (192 : Vertex) (202 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 36 = false ∨ valuation q 49 = false ∨ valuation q 56 = false := by
  rw [value36, value38, value49, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (192 : Vertex) (210 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 42 = false ∨ valuation q 49 = false ∨ valuation q 56 = false := by
  rw [value38, value42, value49, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (202 : Vertex) (210 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 165 = true ∨ valuation q 36 = true ∨ valuation q 42 = true ∨ valuation q 49 = true ∨ valuation q 56 = true := by
  rw [value36, value38, value42, value49, value56, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(192 : Vertex), (202 : Vertex), (210 : Vertex), (226 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (66 : Vertex) [(192 : Vertex), (202 : Vertex), (210 : Vertex), (226 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 165 = true ∨ valuation q 2 = true ∨ valuation q 36 = true ∨ valuation q 49 = true ∨ valuation q 56 = true := by
  rw [value2, value36, value38, value49, value56, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(66 : Vertex), (192 : Vertex), (210 : Vertex), (226 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (202 : Vertex) [(66 : Vertex), (192 : Vertex), (210 : Vertex), (226 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 36 = false ∨ valuation q 40 = false ∨ valuation q 44 = false := by
  rw [value36, value39, value40, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (192 : Vertex) (197 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 36 = false ∨ valuation q 40 = false ∨ valuation q 50 = false := by
  rw [value36, value39, value40, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (192 : Vertex) (197 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 36 = false ∨ valuation q 44 = false ∨ valuation q 50 = false := by
  rw [value36, value39, value44, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (192 : Vertex) (204 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 44 = false ∨ valuation q 50 = false := by
  rw [value39, value40, value44, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (197 : Vertex) (204 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 44 = false ∨ valuation q 50 = false ∨ valuation q 105 = false := by
  rw [value39, value44, value50, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (204 : Vertex) (212 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 166 = true ∨ valuation q 36 = true ∨ valuation q 40 = true ∨ valuation q 44 = true ∨ valuation q 50 = true := by
  rw [value36, value39, value40, value44, value50, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(192 : Vertex), (197 : Vertex), (204 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (196 : Vertex) (452 : Vertex) [(192 : Vertex), (197 : Vertex), (204 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 3 = false ∨ valuation q 37 = false ∨ valuation q 58 = false := by
  rw [value3, value37, value40, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (193 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 3 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value3, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (196 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 3 = false ∨ valuation q 41 = false ∨ valuation q 45 = false := by
  rw [value3, value40, value41, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 3 = false ∨ valuation q 41 = false ∨ valuation q 58 = false := by
  rw [value3, value40, value41, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (199 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 3 = false ∨ valuation q 45 = false ∨ valuation q 58 = false := by
  rw [value3, value40, value45, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (205 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 58 = false := by
  rw [value37, value39, value40, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (196 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 37 = false ∨ valuation q 41 = false ∨ valuation q 45 = false := by
  rw [value37, value40, value41, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 37 = false ∨ valuation q 41 = false ∨ valuation q 58 = false := by
  rw [value37, value40, value41, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (199 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 37 = false ∨ valuation q 45 = false ∨ valuation q 58 = false := by
  rw [value37, value40, value45, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (205 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 45 = false := by
  rw [value39, value40, value41, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (196 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 58 = false := by
  rw [value39, value40, value41, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (196 : Vertex) (199 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 58 = false := by
  rw [value40, value41, value45, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (199 : Vertex) (205 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 167 = true ∨ valuation q 3 = true ∨ valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 45 = true ∨ valuation q 58 = true := by
  rw [value3, value37, value39, value40, value41, value45, value58, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (197 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(69 : Vertex), (193 : Vertex), (196 : Vertex), (199 : Vertex), (205 : Vertex), (229 : Vertex)] := by decide
  have hg := other_cover q (197 : Vertex) (453 : Vertex) [(69 : Vertex), (193 : Vertex), (196 : Vertex), (199 : Vertex), (205 : Vertex), (229 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 5 = false ∨ valuation q 40 = false ∨ valuation q 46 = false := by
  rw [value5, value40, value41, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (71 : Vertex) (197 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 5 = false ∨ valuation q 40 = false ∨ valuation q 51 = false := by
  rw [value5, value40, value41, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (71 : Vertex) (197 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 5 = false ∨ valuation q 46 = false ∨ valuation q 51 = false := by
  rw [value5, value41, value46, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (71 : Vertex) (207 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 40 = false ∨ valuation q 46 = false ∨ valuation q 51 = false := by
  rw [value40, value41, value46, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (197 : Vertex) (207 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 168 = true ∨ valuation q 40 = true ∨ valuation q 46 = true ∨ valuation q 51 = true := by
  rw [value40, value41, value46, value51, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(197 : Vertex), (207 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (71 : Vertex) [(197 : Vertex), (207 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E260.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112260
