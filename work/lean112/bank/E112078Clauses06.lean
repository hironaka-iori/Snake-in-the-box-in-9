import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 2 = false ∨ valuation q 38 = false ∨ valuation q 103 = false := by
  rw [value2, value38, value40, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (193 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 2 = false ∨ valuation q 39 = false ∨ valuation q 52 = false := by
  rw [value2, value39, value40, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (194 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 2 = false ∨ valuation q 39 = false ∨ valuation q 103 = false := by
  rw [value2, value39, value40, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (194 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 2 = false ∨ valuation q 42 = false ∨ valuation q 52 = false := by
  rw [value2, value40, value42, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (199 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 2 = false ∨ valuation q 42 = false ∨ valuation q 103 = false := by
  rw [value2, value40, value42, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (199 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 2 = false ∨ valuation q 52 = false ∨ valuation q 103 = false := by
  rw [value2, value40, value52, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (211 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 20 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value20, value38, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (193 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 20 = false ∨ valuation q 38 = false ∨ valuation q 42 = false := by
  rw [value20, value38, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (193 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 20 = false ∨ valuation q 38 = false ∨ valuation q 52 = false := by
  rw [value20, value38, value40, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (193 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 20 = false ∨ valuation q 38 = false ∨ valuation q 103 = false := by
  rw [value20, value38, value40, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (193 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 20 = false ∨ valuation q 39 = false ∨ valuation q 42 = false := by
  rw [value20, value39, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (194 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 20 = false ∨ valuation q 39 = false ∨ valuation q 52 = false := by
  rw [value20, value39, value40, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (194 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 20 = false ∨ valuation q 39 = false ∨ valuation q 103 = false := by
  rw [value20, value39, value40, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (194 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 20 = false ∨ valuation q 42 = false ∨ valuation q 52 = false := by
  rw [value20, value40, value42, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (199 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 20 = false ∨ valuation q 42 = false ∨ valuation q 103 = false := by
  rw [value20, value40, value42, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (199 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 20 = false ∨ valuation q 52 = false ∨ valuation q 103 = false := by
  rw [value20, value40, value52, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (211 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 42 = false := by
  rw [value38, value39, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (194 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 52 = false := by
  rw [value38, value39, value40, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (194 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 103 = false := by
  rw [value38, value39, value40, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (194 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 38 = false ∨ valuation q 42 = false ∨ valuation q 52 = false := by
  rw [value38, value40, value42, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (199 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 38 = false ∨ valuation q 42 = false ∨ valuation q 103 = false := by
  rw [value38, value40, value42, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (199 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 38 = false ∨ valuation q 52 = false ∨ valuation q 103 = false := by
  rw [value38, value40, value52, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (211 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 52 = false := by
  rw [value39, value40, value42, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (194 : Vertex) (199 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 103 = false := by
  rw [value39, value40, value42, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (194 : Vertex) (199 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 52 = false ∨ valuation q 103 = false := by
  rw [value39, value40, value52, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (194 : Vertex) (211 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 52 = false ∨ valuation q 103 = false := by
  rw [value40, value42, value52, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (199 : Vertex) (211 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 159 = true ∨ valuation q 2 = true ∨ valuation q 20 = true ∨ valuation q 39 = true ∨ valuation q 42 = true ∨ valuation q 52 = true ∨ valuation q 103 = true := by
  rw [value2, value20, value39, value40, value42, value52, value103, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (195 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(67 : Vertex), (131 : Vertex), (194 : Vertex), (199 : Vertex), (211 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (195 : Vertex) (193 : Vertex) [(67 : Vertex), (131 : Vertex), (194 : Vertex), (199 : Vertex), (211 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 159 = true ∨ valuation q 2 = true ∨ valuation q 20 = true ∨ valuation q 38 = true ∨ valuation q 42 = true ∨ valuation q 52 = true ∨ valuation q 103 = true := by
  rw [value2, value20, value38, value40, value42, value52, value103, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (195 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(67 : Vertex), (131 : Vertex), (193 : Vertex), (199 : Vertex), (211 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (195 : Vertex) (194 : Vertex) [(67 : Vertex), (131 : Vertex), (193 : Vertex), (199 : Vertex), (211 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 159 = true ∨ valuation q 2 = true ∨ valuation q 20 = true ∨ valuation q 38 = true ∨ valuation q 39 = true ∨ valuation q 52 = true ∨ valuation q 103 = true := by
  rw [value2, value20, value38, value39, value40, value52, value103, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (195 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(67 : Vertex), (131 : Vertex), (193 : Vertex), (194 : Vertex), (211 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (195 : Vertex) (199 : Vertex) [(67 : Vertex), (131 : Vertex), (193 : Vertex), (194 : Vertex), (211 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 159 = true ∨ valuation q 2 = true ∨ valuation q 20 = true ∨ valuation q 38 = true ∨ valuation q 39 = true ∨ valuation q 42 = true ∨ valuation q 52 = true := by
  rw [value2, value20, value38, value39, value40, value42, value52, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (195 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(67 : Vertex), (131 : Vertex), (193 : Vertex), (194 : Vertex), (199 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (195 : Vertex) (451 : Vertex) [(67 : Vertex), (131 : Vertex), (193 : Vertex), (194 : Vertex), (199 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 4 = false ∨ valuation q 38 = false ∨ valuation q 42 = false := by
  rw [value4, value38, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (193 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 4 = false ∨ valuation q 38 = false ∨ valuation q 46 = false := by
  rw [value4, value38, value41, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (193 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E078.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112078
