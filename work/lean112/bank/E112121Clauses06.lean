import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 27 = false ∨ valuation q 36 = false ∨ valuation q 74 = false := by
  rw [value16, value27, value36, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (57 : Vertex) (105 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 19 = false := by
  rw [value10, value15, value17, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (34 : Vertex) (40 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 28 = false := by
  rw [value10, value15, value17, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (34 : Vertex) (40 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 28 = false := by
  rw [value10, value17, value19, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (34 : Vertex) (46 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 28 = false := by
  rw [value15, value17, value19, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (40 : Vertex) (46 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 143 = true ∨ valuation q 10 = true ∨ valuation q 15 = true ∨ valuation q 28 = true := by
  rw [value10, value15, value17, value28, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(34 : Vertex), (40 : Vertex), (58 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (46 : Vertex) [(34 : Vertex), (40 : Vertex), (58 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 143 = true ∨ valuation q 10 = true ∨ valuation q 15 = true ∨ valuation q 19 = true := by
  rw [value10, value15, value17, value19, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(34 : Vertex), (40 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (58 : Vertex) [(34 : Vertex), (40 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 19 = false := by
  rw [value11, value15, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (44 : Vertex) (36 : Vertex) (40 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 144 = true ∨ valuation q 15 = true ∨ valuation q 19 = true := by
  rw [value15, value18, value19, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (44 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(40 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (44 : Vertex) (36 : Vertex) [(40 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 144 = true ∨ valuation q 11 = true ∨ valuation q 15 = true := by
  rw [value11, value15, value18, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (44 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(36 : Vertex), (40 : Vertex)] := by decide
  have hg := other_cover q (44 : Vertex) (46 : Vertex) [(36 : Vertex), (40 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 145 = true ∨ valuation q 17 = true ∨ valuation q 18 = true ∨ valuation q 30 = true := by
  rw [value17, value18, value19, value30, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (46 : Vertex) w → w ∈ region → w ≠ (38 : Vertex) → w ∈ [(42 : Vertex), (44 : Vertex), (62 : Vertex)] := by decide
  have hg := other_cover q (46 : Vertex) (38 : Vertex) [(42 : Vertex), (44 : Vertex), (62 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 145 = true ∨ valuation q 13 = true ∨ valuation q 18 = true ∨ valuation q 30 = true := by
  rw [value13, value18, value19, value30, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (46 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(38 : Vertex), (44 : Vertex), (62 : Vertex)] := by decide
  have hg := other_cover q (46 : Vertex) (42 : Vertex) [(38 : Vertex), (44 : Vertex), (62 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 145 = true ∨ valuation q 13 = true ∨ valuation q 17 = true ∨ valuation q 30 = true := by
  rw [value13, value17, value19, value30, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (46 : Vertex) w → w ∈ region → w ≠ (44 : Vertex) → w ∈ [(38 : Vertex), (42 : Vertex), (62 : Vertex)] := by decide
  have hg := other_cover q (46 : Vertex) (44 : Vertex) [(38 : Vertex), (42 : Vertex), (62 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 145 = true ∨ valuation q 13 = true ∨ valuation q 17 = true ∨ valuation q 18 = true := by
  rw [value13, value17, value18, value19, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (46 : Vertex) w → w ∈ region → w ≠ (62 : Vertex) → w ∈ [(38 : Vertex), (42 : Vertex), (44 : Vertex)] := by decide
  have hg := other_cover q (46 : Vertex) (62 : Vertex) [(38 : Vertex), (42 : Vertex), (44 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 22 = false := by
  rw [value4, value9, value20, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (33 : Vertex) (51 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 24 = false := by
  rw [value4, value9, value20, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (33 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 27 = false := by
  rw [value4, value9, value20, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (33 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 53 = false := by
  rw [value4, value9, value20, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (33 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 78 = false := by
  rw [value4, value9, value20, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (33 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 22 = false ∨ valuation q 24 = false := by
  rw [value4, value20, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (51 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 22 = false ∨ valuation q 27 = false := by
  rw [value4, value20, value22, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (51 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 22 = false ∨ valuation q 53 = false := by
  rw [value4, value20, value22, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (51 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 24 = false ∨ valuation q 27 = false := by
  rw [value4, value20, value24, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (53 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 24 = false ∨ valuation q 53 = false := by
  rw [value4, value20, value24, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (53 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 24 = false ∨ valuation q 78 = false := by
  rw [value4, value20, value24, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (53 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 27 = false ∨ valuation q 53 = false := by
  rw [value4, value20, value27, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (57 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 27 = false ∨ valuation q 78 = false := by
  rw [value4, value20, value27, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (57 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 4 = false ∨ valuation q 53 = false ∨ valuation q 78 = false := by
  rw [value4, value20, value53, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (177 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 22 = false ∨ valuation q 24 = false := by
  rw [value9, value20, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (33 : Vertex) (51 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 22 = false ∨ valuation q 27 = false := by
  rw [value9, value20, value22, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (33 : Vertex) (51 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 22 = false ∨ valuation q 53 = false := by
  rw [value9, value20, value22, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (33 : Vertex) (51 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 24 = false ∨ valuation q 27 = false := by
  rw [value9, value20, value24, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (33 : Vertex) (53 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E121.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112121
