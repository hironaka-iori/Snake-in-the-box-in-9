import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 154 = true ∨ valuation q 34 = true ∨ valuation q 36 = true := by
  rw [value34, value36, value37, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(91 : Vertex), (94 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (79 : Vertex) [(91 : Vertex), (94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 154 = true ∨ valuation q 26 = true ∨ valuation q 36 = true := by
  rw [value26, value36, value37, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(79 : Vertex), (94 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (91 : Vertex) [(79 : Vertex), (94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 154 = true ∨ valuation q 26 = true ∨ valuation q 34 = true := by
  rw [value26, value34, value37, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(79 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (94 : Vertex) [(79 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 1 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value1, value38, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (129 : Vertex) (130 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 1 = false ∨ valuation q 39 = false ∨ valuation q 56 = false := by
  rw [value1, value38, value39, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (129 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 1 = false ∨ valuation q 40 = false ∨ valuation q 46 = false := by
  rw [value1, value38, value40, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (130 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 1 = false ∨ valuation q 40 = false ∨ valuation q 56 = false := by
  rw [value1, value38, value40, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (130 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 1 = false ∨ valuation q 46 = false ∨ valuation q 56 = false := by
  rw [value1, value38, value46, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (144 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 56 = false := by
  rw [value38, value39, value40, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (129 : Vertex) (130 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 46 = false ∨ valuation q 56 = false := by
  rw [value38, value39, value46, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (129 : Vertex) (144 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 46 = false ∨ valuation q 56 = false := by
  rw [value38, value40, value46, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (130 : Vertex) (144 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 2 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value2, value39, value41, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (1 : Vertex) (131 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 2 = false ∨ valuation q 41 = false ∨ valuation q 57 = false := by
  rw [value2, value39, value41, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (1 : Vertex) (131 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 2 = false ∨ valuation q 43 = false ∨ valuation q 47 = false := by
  rw [value2, value39, value43, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (1 : Vertex) (137 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 2 = false ∨ valuation q 43 = false ∨ valuation q 57 = false := by
  rw [value2, value39, value43, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (1 : Vertex) (137 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 38 = false ∨ valuation q 43 = false ∨ valuation q 47 = false := by
  rw [value38, value39, value43, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (128 : Vertex) (137 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 43 = false ∨ valuation q 47 = false ∨ valuation q 57 = false := by
  rw [value39, value43, value47, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (137 : Vertex) (145 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 157 = true ∨ valuation q 41 = true ∨ valuation q 48 = true := by
  rw [value40, value41, value48, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(131 : Vertex), (146 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (128 : Vertex) [(131 : Vertex), (146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 157 = true ∨ valuation q 38 = true ∨ valuation q 48 = true := by
  rw [value38, value40, value48, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(128 : Vertex), (146 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (131 : Vertex) [(128 : Vertex), (146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 157 = true ∨ valuation q 38 = true ∨ valuation q 41 = true := by
  rw [value38, value40, value41, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(128 : Vertex), (131 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (146 : Vertex) [(128 : Vertex), (131 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 42 = false := by
  rw [value39, value40, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (129 : Vertex) (130 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 49 = false := by
  rw [value39, value41, value42, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (129 : Vertex) (135 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 49 = false := by
  rw [value40, value41, value42, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (130 : Vertex) (135 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 158 = true ∨ valuation q 39 = true ∨ valuation q 40 = true ∨ valuation q 42 = true := by
  rw [value39, value40, value41, value42, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(129 : Vertex), (130 : Vertex), (135 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (147 : Vertex) [(129 : Vertex), (130 : Vertex), (135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 60 = false := by
  rw [value41, value42, value45, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (143 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 92 = false := by
  rw [value41, value42, value45, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (143 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 41 = false ∨ valuation q 60 = false ∨ valuation q 92 = false := by
  rw [value41, value42, value60, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 60 = false ∨ valuation q 92 = false := by
  rw [value42, value45, value60, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (143 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 39 = false ∨ valuation q 44 = false ∨ valuation q 62 = false := by
  rw [value39, value43, value44, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (129 : Vertex) (141 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 39 = false ∨ valuation q 44 = false ∨ valuation q 93 = false := by
  rw [value39, value43, value44, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (129 : Vertex) (141 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 39 = false ∨ valuation q 62 = false ∨ valuation q 93 = false := by
  rw [value39, value43, value62, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (129 : Vertex) (201 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 62 = false ∨ valuation q 93 = false := by
  rw [value43, value44, value62, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (141 : Vertex) (201 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E213.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112213
