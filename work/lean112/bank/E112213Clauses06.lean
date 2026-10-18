import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 27 = false ∨ valuation q 33 = false ∨ valuation q 66 = false := by
  rw [value27, value29, value33, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (80 : Vertex) (90 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 27 = false ∨ valuation q 33 = false ∨ valuation q 83 = false := by
  rw [value27, value29, value33, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (80 : Vertex) (90 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 27 = false ∨ valuation q 66 = false ∨ valuation q 83 = false := by
  rw [value27, value29, value66, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (80 : Vertex) (210 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 66 = false := by
  rw [value29, value30, value33, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (83 : Vertex) (90 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 83 = false := by
  rw [value29, value30, value33, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (83 : Vertex) (90 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 66 = false ∨ valuation q 83 = false := by
  rw [value29, value30, value66, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (83 : Vertex) (210 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 33 = false ∨ valuation q 66 = false ∨ valuation q 83 = false := by
  rw [value29, value33, value66, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (90 : Vertex) (210 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 147 = true ∨ valuation q 28 = true ∨ valuation q 29 = true ∨ valuation q 34 = true := by
  rw [value28, value29, value30, value34, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (67 : Vertex) → w ∈ [(81 : Vertex), (82 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (67 : Vertex) [(81 : Vertex), (82 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 147 = true ∨ valuation q 18 = true ∨ valuation q 29 = true ∨ valuation q 34 = true := by
  rw [value18, value29, value30, value34, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (81 : Vertex) → w ∈ [(67 : Vertex), (82 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (81 : Vertex) [(67 : Vertex), (82 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 147 = true ∨ valuation q 18 = true ∨ valuation q 28 = true ∨ valuation q 34 = true := by
  rw [value18, value28, value30, value34, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(67 : Vertex), (81 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (82 : Vertex) [(67 : Vertex), (81 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 147 = true ∨ valuation q 18 = true ∨ valuation q 28 = true ∨ valuation q 29 = true := by
  rw [value18, value28, value29, value30, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(67 : Vertex), (81 : Vertex), (82 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (91 : Vertex) [(67 : Vertex), (81 : Vertex), (82 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 27 = false ∨ valuation q 35 = false ∨ valuation q 84 = false := by
  rw [value27, value31, value35, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (80 : Vertex) (92 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 148 = true ∨ valuation q 27 = true ∨ valuation q 35 = true := by
  rw [value27, value31, value35, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(80 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (340 : Vertex) [(80 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 21 = false ∨ valuation q 27 = false ∨ valuation q 33 = false := by
  rw [value21, value27, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (72 : Vertex) (80 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 21 = false ∨ valuation q 27 = false ∨ valuation q 35 = false := by
  rw [value21, value27, value32, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (72 : Vertex) (80 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 21 = false ∨ valuation q 33 = false ∨ valuation q 35 = false := by
  rw [value21, value32, value33, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (72 : Vertex) (90 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 27 = false ∨ valuation q 33 = false ∨ valuation q 35 = false := by
  rw [value27, value32, value33, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (80 : Vertex) (90 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 29 = false ∨ valuation q 34 = false ∨ valuation q 71 = false := by
  rw [value29, value33, value34, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (82 : Vertex) (91 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 29 = false ∨ valuation q 36 = false ∨ valuation q 89 = false := by
  rw [value29, value33, value36, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (82 : Vertex) (94 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 71 = false := by
  rw [value33, value34, value36, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (91 : Vertex) (94 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 71 = false ∨ valuation q 89 = false := by
  rw [value33, value34, value71, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (91 : Vertex) (218 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 71 = false ∨ valuation q 89 = false := by
  rw [value33, value36, value71, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (94 : Vertex) (218 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 30 = false := by
  rw [value13, value22, value30, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (27 : Vertex) (75 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 33 = false := by
  rw [value13, value22, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (27 : Vertex) (75 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 37 = false := by
  rw [value13, value22, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (27 : Vertex) (75 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 72 = false := by
  rw [value13, value22, value34, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (27 : Vertex) (75 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 90 = false := by
  rw [value13, value22, value34, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (27 : Vertex) (75 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 13 = false ∨ valuation q 30 = false ∨ valuation q 33 = false := by
  rw [value13, value30, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (27 : Vertex) (83 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 13 = false ∨ valuation q 30 = false ∨ valuation q 37 = false := by
  rw [value13, value30, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (27 : Vertex) (83 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 13 = false ∨ valuation q 30 = false ∨ valuation q 72 = false := by
  rw [value13, value30, value34, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (27 : Vertex) (83 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 13 = false ∨ valuation q 30 = false ∨ valuation q 90 = false := by
  rw [value13, value30, value34, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (27 : Vertex) (83 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 13 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value13, value33, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (27 : Vertex) (90 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E213.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112213
