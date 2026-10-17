import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 57 = false ∨ valuation q 98 = false := by
  rw [value44, value45, value57, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (194 : Vertex) (211 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 57 = false ∨ valuation q 98 = false := by
  rw [value45, value47, value57, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (199 : Vertex) (211 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 24 = false ∨ valuation q 43 = false := by
  rw [value24, value43, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (195 : Vertex) (131 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 24 = false ∨ valuation q 44 = false := by
  rw [value24, value44, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (195 : Vertex) (131 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 43 = false ∨ valuation q 47 = false ∨ valuation q 51 = false := by
  rw [value43, value46, value47, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 43 = false ∨ valuation q 47 = false ∨ valuation q 100 = false := by
  rw [value43, value46, value47, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (199 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 43 = false ∨ valuation q 51 = false ∨ valuation q 100 = false := by
  rw [value43, value46, value51, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (205 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 100 = false := by
  rw [value46, value47, value51, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (199 : Vertex) (205 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 27 = false ∨ valuation q 45 = false ∨ valuation q 46 = false := by
  rw [value27, value45, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (135 : Vertex) (195 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 27 = false ∨ valuation q 45 = false ∨ valuation q 53 = false := by
  rw [value27, value45, value47, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (135 : Vertex) (195 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 161 = true ∨ valuation q 45 = true ∨ valuation q 46 = true ∨ valuation q 53 = true := by
  rw [value45, value46, value47, value53, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(195 : Vertex), (197 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (135 : Vertex) [(195 : Vertex), (197 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 161 = true ∨ valuation q 27 = true ∨ valuation q 46 = true ∨ valuation q 53 = true := by
  rw [value27, value46, value47, value53, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(135 : Vertex), (197 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (195 : Vertex) [(135 : Vertex), (197 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 161 = true ∨ valuation q 27 = true ∨ valuation q 45 = true ∨ valuation q 53 = true := by
  rw [value27, value45, value47, value53, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(135 : Vertex), (195 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (197 : Vertex) [(135 : Vertex), (195 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 161 = true ∨ valuation q 27 = true ∨ valuation q 45 = true ∨ valuation q 46 = true := by
  rw [value27, value45, value46, value47, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(135 : Vertex), (195 : Vertex), (197 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (207 : Vertex) [(135 : Vertex), (195 : Vertex), (197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 10 = false ∨ valuation q 29 = false ∨ valuation q 43 = false := by
  rw [value10, value29, value43, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (137 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 10 = false ∨ valuation q 29 = false ∨ valuation q 51 = false := by
  rw [value10, value29, value48, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (137 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 10 = false ∨ valuation q 29 = false ∨ valuation q 60 = false := by
  rw [value10, value29, value48, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (137 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 10 = false ∨ valuation q 43 = false ∨ valuation q 51 = false := by
  rw [value10, value43, value48, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (193 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 10 = false ∨ valuation q 43 = false ∨ valuation q 60 = false := by
  rw [value10, value43, value48, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (193 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 10 = false ∨ valuation q 43 = false ∨ valuation q 101 = false := by
  rw [value10, value43, value48, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (193 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 10 = false ∨ valuation q 51 = false ∨ valuation q 60 = false := by
  rw [value10, value48, value51, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (205 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 10 = false ∨ valuation q 51 = false ∨ valuation q 101 = false := by
  rw [value10, value48, value51, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (205 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 29 = false ∨ valuation q 43 = false ∨ valuation q 51 = false := by
  rw [value29, value43, value48, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 29 = false ∨ valuation q 43 = false ∨ valuation q 60 = false := by
  rw [value29, value43, value48, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 29 = false ∨ valuation q 43 = false ∨ valuation q 101 = false := by
  rw [value29, value43, value48, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 29 = false ∨ valuation q 51 = false ∨ valuation q 60 = false := by
  rw [value29, value48, value51, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (205 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 29 = false ∨ valuation q 51 = false ∨ valuation q 101 = false := by
  rw [value29, value48, value51, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (205 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 29 = false ∨ valuation q 60 = false ∨ valuation q 101 = false := by
  rw [value29, value48, value60, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (217 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 43 = false ∨ valuation q 51 = false ∨ valuation q 60 = false := by
  rw [value43, value48, value51, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (205 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 43 = false ∨ valuation q 51 = false ∨ valuation q 101 = false := by
  rw [value43, value48, value51, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (205 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 43 = false ∨ valuation q 60 = false ∨ valuation q 101 = false := by
  rw [value43, value48, value60, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (217 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 101 = false := by
  rw [value48, value51, value60, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (205 : Vertex) (217 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E168.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112168
