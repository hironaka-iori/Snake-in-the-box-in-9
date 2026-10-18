import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value34, value35, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value34, value36, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (230 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 150 = true ∨ valuation q 32 = true ∨ valuation q 35 = true ∨ valuation q 42 = true ∨ valuation q 45 = true := by
  rw [value32, value34, value35, value42, value45, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (228 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [(224 : Vertex), (229 : Vertex), (236 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (228 : Vertex) (230 : Vertex) [(224 : Vertex), (229 : Vertex), (236 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 2 = false ∨ valuation q 15 = false ∨ valuation q 37 = false := by
  rw [value2, value15, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (101 : Vertex) (165 : Vertex) (231 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 2 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value2, value34, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (101 : Vertex) (228 : Vertex) (231 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 2 = false ∨ valuation q 34 = false ∨ valuation q 102 = false := by
  rw [value2, value34, value35, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (101 : Vertex) (228 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 2 = false ∨ valuation q 37 = false ∨ valuation q 46 = false := by
  rw [value2, value35, value37, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (101 : Vertex) (231 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 2 = false ∨ valuation q 37 = false ∨ valuation q 102 = false := by
  rw [value2, value35, value37, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (101 : Vertex) (231 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 2 = false ∨ valuation q 46 = false ∨ valuation q 102 = false := by
  rw [value2, value35, value46, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (101 : Vertex) (245 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 15 = false ∨ valuation q 34 = false ∨ valuation q 46 = false := by
  rw [value15, value34, value35, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (165 : Vertex) (228 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 15 = false ∨ valuation q 37 = false ∨ valuation q 46 = false := by
  rw [value15, value35, value37, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (165 : Vertex) (231 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 43 = false := by
  rw [value34, value36, value37, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (230 : Vertex) (228 : Vertex) (231 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 152 = true ∨ valuation q 37 = true ∨ valuation q 43 = true := by
  rw [value36, value37, value43, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(231 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (228 : Vertex) [(231 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 152 = true ∨ valuation q 34 = true ∨ valuation q 43 = true := by
  rw [value34, value36, value43, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (231 : Vertex) → w ∈ [(228 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (231 : Vertex) [(228 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 152 = true ∨ valuation q 34 = true ∨ valuation q 37 = true := by
  rw [value34, value36, value37, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(228 : Vertex), (231 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (238 : Vertex) [(228 : Vertex), (231 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 16 = false ∨ valuation q 33 = false := by
  rw [value3, value16, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (167 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 16 = false ∨ valuation q 35 = false := by
  rw [value3, value16, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (167 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 16 = false ∨ valuation q 36 = false := by
  rw [value3, value16, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (167 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 16 = false ∨ valuation q 47 = false := by
  rw [value3, value16, value37, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (167 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 16 = false ∨ valuation q 103 = false := by
  rw [value3, value16, value37, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (167 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 33 = false ∨ valuation q 35 = false := by
  rw [value3, value33, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (227 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 33 = false ∨ valuation q 36 = false := by
  rw [value3, value33, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (227 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 33 = false ∨ valuation q 47 = false := by
  rw [value3, value33, value37, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (227 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 33 = false ∨ valuation q 103 = false := by
  rw [value3, value33, value37, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (227 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value3, value35, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (229 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 35 = false ∨ valuation q 47 = false := by
  rw [value3, value35, value37, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (229 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 36 = false ∨ valuation q 47 = false := by
  rw [value3, value36, value37, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (230 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 36 = false ∨ valuation q 103 = false := by
  rw [value3, value36, value37, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (230 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 47 = false ∨ valuation q 103 = false := by
  rw [value3, value37, value47, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (247 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 16 = false ∨ valuation q 33 = false ∨ valuation q 35 = false := by
  rw [value16, value33, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (167 : Vertex) (227 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 16 = false ∨ valuation q 33 = false ∨ valuation q 36 = false := by
  rw [value16, value33, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (167 : Vertex) (227 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 16 = false ∨ valuation q 33 = false ∨ valuation q 47 = false := by
  rw [value16, value33, value37, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (167 : Vertex) (227 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E088.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112088
