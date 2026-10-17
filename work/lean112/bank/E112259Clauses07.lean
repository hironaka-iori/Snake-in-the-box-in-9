import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 169 = true ∨ valuation q 116 = true := by
  rw [value53, value116, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (127 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(255 : Vertex)] := by decide
  have hg := other_cover q (127 : Vertex) (125 : Vertex) [(255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 169 = true ∨ valuation q 52 = true := by
  rw [value52, value53, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (127 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(125 : Vertex)] := by decide
  have hg := other_cover q (127 : Vertex) (255 : Vertex) [(125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 1 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value1, value54, value55, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (129 : Vertex) (132 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 1 = false ∨ valuation q 55 = false ∨ valuation q 60 = false := by
  rw [value1, value54, value55, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (129 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 1 = false ∨ valuation q 55 = false ∨ valuation q 75 = false := by
  rw [value1, value54, value55, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (129 : Vertex) (160 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 1 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value1, value54, value57, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (132 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 1 = false ∨ valuation q 57 = false ∨ valuation q 75 = false := by
  rw [value1, value54, value57, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (132 : Vertex) (160 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 1 = false ∨ valuation q 60 = false ∨ valuation q 75 = false := by
  rw [value1, value54, value60, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (136 : Vertex) (160 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value54, value55, value57, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (129 : Vertex) (132 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 75 = false := by
  rw [value54, value55, value57, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (129 : Vertex) (132 : Vertex) (160 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 60 = false ∨ valuation q 75 = false := by
  rw [value54, value55, value60, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (129 : Vertex) (136 : Vertex) (160 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 57 = false ∨ valuation q 60 = false ∨ valuation q 75 = false := by
  rw [value54, value57, value60, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (132 : Vertex) (136 : Vertex) (160 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 1 = false ∨ valuation q 55 = false := by
  rw [value1, value55, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (128 : Vertex) (0 : Vertex) (129 : Vertex) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 1 = false ∨ valuation q 60 = false := by
  rw [value1, value60, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (128 : Vertex) (0 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 1 = false ∨ valuation q 75 = false := by
  rw [value1, value75, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (128 : Vertex) (0 : Vertex) (160 : Vertex) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 170 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 60 = true ∨ valuation q 75 = true := by
  rw [value54, value55, value57, value60, value75, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (128 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(129 : Vertex), (132 : Vertex), (136 : Vertex), (160 : Vertex)] := by decide
  have hg := other_cover q (128 : Vertex) (0 : Vertex) [(129 : Vertex), (132 : Vertex), (136 : Vertex), (160 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 170 = true ∨ valuation q 1 = true ∨ valuation q 57 = true ∨ valuation q 60 = true ∨ valuation q 75 = true := by
  rw [value1, value54, value57, value60, value75, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (128 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(0 : Vertex), (132 : Vertex), (136 : Vertex), (160 : Vertex)] := by decide
  have hg := other_cover q (128 : Vertex) (129 : Vertex) [(0 : Vertex), (132 : Vertex), (136 : Vertex), (160 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 170 = true ∨ valuation q 1 = true ∨ valuation q 55 = true ∨ valuation q 60 = true ∨ valuation q 75 = true := by
  rw [value1, value54, value55, value60, value75, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (128 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(0 : Vertex), (129 : Vertex), (136 : Vertex), (160 : Vertex)] := by decide
  have hg := other_cover q (128 : Vertex) (132 : Vertex) [(0 : Vertex), (129 : Vertex), (136 : Vertex), (160 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 58 = false := by
  rw [value54, value55, value56, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (128 : Vertex) (131 : Vertex) (133 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 61 = false := by
  rw [value54, value55, value56, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (128 : Vertex) (131 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 76 = false := by
  rw [value54, value55, value56, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (128 : Vertex) (131 : Vertex) (161 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 54 = false ∨ valuation q 61 = false ∨ valuation q 76 = false := by
  rw [value54, value55, value61, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (128 : Vertex) (137 : Vertex) (161 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 76 = false := by
  rw [value55, value56, value58, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (133 : Vertex) (161 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 61 = false ∨ valuation q 76 = false := by
  rw [value55, value56, value61, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (137 : Vertex) (161 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 171 = true ∨ valuation q 56 = true ∨ valuation q 58 = true ∨ valuation q 61 = true ∨ valuation q 76 = true := by
  rw [value55, value56, value58, value61, value76, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(131 : Vertex), (133 : Vertex), (137 : Vertex), (161 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (128 : Vertex) [(131 : Vertex), (133 : Vertex), (137 : Vertex), (161 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 171 = true ∨ valuation q 54 = true ∨ valuation q 58 = true ∨ valuation q 61 = true ∨ valuation q 76 = true := by
  rw [value54, value55, value58, value61, value76, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(128 : Vertex), (133 : Vertex), (137 : Vertex), (161 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (131 : Vertex) [(128 : Vertex), (133 : Vertex), (137 : Vertex), (161 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 171 = true ∨ valuation q 54 = true ∨ valuation q 56 = true ∨ valuation q 61 = true ∨ valuation q 76 = true := by
  rw [value54, value55, value56, value61, value76, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(128 : Vertex), (131 : Vertex), (137 : Vertex), (161 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (133 : Vertex) [(128 : Vertex), (131 : Vertex), (137 : Vertex), (161 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 171 = true ∨ valuation q 54 = true ∨ valuation q 56 = true ∨ valuation q 58 = true ∨ valuation q 76 = true := by
  rw [value54, value55, value56, value58, value76, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(128 : Vertex), (131 : Vertex), (133 : Vertex), (161 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (137 : Vertex) [(128 : Vertex), (131 : Vertex), (133 : Vertex), (161 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 171 = true ∨ valuation q 54 = true ∨ valuation q 56 = true ∨ valuation q 58 = true ∨ valuation q 61 = true := by
  rw [value54, value55, value56, value58, value61, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(128 : Vertex), (131 : Vertex), (133 : Vertex), (137 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (161 : Vertex) [(128 : Vertex), (131 : Vertex), (133 : Vertex), (137 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 2 = false ∨ valuation q 55 = false ∨ valuation q 62 = false := by
  rw [value2, value55, value56, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (3 : Vertex) (129 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 2 = false ∨ valuation q 55 = false ∨ valuation q 66 = false := by
  rw [value2, value55, value56, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (3 : Vertex) (129 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 2 = false ∨ valuation q 55 = false ∨ valuation q 78 = false := by
  rw [value2, value55, value56, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (3 : Vertex) (129 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E259.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112259
