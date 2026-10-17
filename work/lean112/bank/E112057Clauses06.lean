import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 148 = true ∨ valuation q 25 = true ∨ valuation q 94 = true := by
  rw [value21, value25, value94, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(71 : Vertex), (323 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (75 : Vertex) [(71 : Vertex), (323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 149 = true ∨ valuation q 24 = true ∨ valuation q 32 = true := by
  rw [value22, value24, value32, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(70 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (69 : Vertex) [(70 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 149 = true ∨ valuation q 23 = true ∨ valuation q 32 = true := by
  rw [value22, value23, value32, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(69 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (70 : Vertex) [(69 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 149 = true ∨ valuation q 23 = true ∨ valuation q 24 = true := by
  rw [value22, value23, value24, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(69 : Vertex), (70 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (84 : Vertex) [(69 : Vertex), (70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 23 = true := by
  rw [value23, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (69 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value4, value22, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (68 : Vertex) (71 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 22 = false ∨ valuation q 33 = false := by
  rw [value4, value22, value23, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (68 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 22 = false ∨ valuation q 59 = false := by
  rw [value4, value22, value23, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (68 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 22 = false ∨ valuation q 95 = false := by
  rw [value4, value22, value23, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (68 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 25 = false ∨ valuation q 33 = false := by
  rw [value4, value23, value25, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (71 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 25 = false ∨ valuation q 59 = false := by
  rw [value4, value23, value25, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (71 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 25 = false ∨ valuation q 95 = false := by
  rw [value4, value23, value25, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (71 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 33 = false ∨ valuation q 59 = false := by
  rw [value4, value23, value33, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (85 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 33 = false ∨ valuation q 95 = false := by
  rw [value4, value23, value33, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (85 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 59 = false ∨ valuation q 95 = false := by
  rw [value4, value23, value59, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (197 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 33 = false := by
  rw [value22, value23, value25, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (68 : Vertex) (71 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 59 = false := by
  rw [value22, value23, value25, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (68 : Vertex) (71 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 95 = false := by
  rw [value22, value23, value25, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (68 : Vertex) (71 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 33 = false ∨ valuation q 59 = false := by
  rw [value22, value23, value33, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (68 : Vertex) (85 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 33 = false ∨ valuation q 95 = false := by
  rw [value22, value23, value33, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (68 : Vertex) (85 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 59 = false ∨ valuation q 95 = false := by
  rw [value22, value23, value59, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (68 : Vertex) (197 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 33 = false ∨ valuation q 59 = false := by
  rw [value23, value25, value33, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (71 : Vertex) (85 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 33 = false ∨ valuation q 95 = false := by
  rw [value23, value25, value33, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (71 : Vertex) (85 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 59 = false ∨ valuation q 95 = false := by
  rw [value23, value25, value59, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (71 : Vertex) (197 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 33 = false ∨ valuation q 59 = false ∨ valuation q 95 = false := by
  rw [value23, value33, value59, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (85 : Vertex) (197 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value22, value25, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (70 : Vertex) (68 : Vertex) (71 : Vertex) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 151 = true ∨ valuation q 25 = true := by
  rw [value24, value25, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(71 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (68 : Vertex) [(71 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 151 = true ∨ valuation q 22 = true := by
  rw [value22, value24, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(68 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (71 : Vertex) [(68 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 29 = false := by
  rw [value21, value23, value25, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (67 : Vertex) (69 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 29 = false := by
  rw [value23, value24, value25, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (69 : Vertex) (70 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 152 = true ∨ valuation q 23 = true ∨ valuation q 24 = true ∨ valuation q 29 = true := by
  rw [value23, value24, value25, value29, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (71 : Vertex) w → w ∈ region → w ≠ (67 : Vertex) → w ∈ [(69 : Vertex), (70 : Vertex), (79 : Vertex)] := by decide
  have hg := other_cover q (71 : Vertex) (67 : Vertex) [(69 : Vertex), (70 : Vertex), (79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 152 = true ∨ valuation q 21 = true ∨ valuation q 23 = true ∨ valuation q 29 = true := by
  rw [value21, value23, value25, value29, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (71 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(67 : Vertex), (69 : Vertex), (79 : Vertex)] := by decide
  have hg := other_cover q (71 : Vertex) (70 : Vertex) [(67 : Vertex), (69 : Vertex), (79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E057.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112057
