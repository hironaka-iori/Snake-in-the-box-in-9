import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 28 = false ∨ valuation q 56 = false := by
  rw [value17, value19, value28, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (76 : Vertex) (94 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 28 = false ∨ valuation q 74 = false := by
  rw [value17, value19, value28, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (76 : Vertex) (94 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 56 = false ∨ valuation q 74 = false := by
  rw [value17, value19, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (76 : Vertex) (206 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 28 = false ∨ valuation q 56 = false := by
  rw [value19, value20, value28, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (79 : Vertex) (94 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 28 = false ∨ valuation q 74 = false := by
  rw [value19, value20, value28, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (79 : Vertex) (94 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 56 = false ∨ valuation q 74 = false := by
  rw [value19, value20, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (79 : Vertex) (206 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 56 = false ∨ valuation q 74 = false := by
  rw [value19, value28, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (94 : Vertex) (206 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 19 = false := by
  rw [value15, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (77 : Vertex) (78 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 29 = false := by
  rw [value15, value18, value20, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (77 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 75 = false := by
  rw [value15, value18, value20, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (77 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 29 = false := by
  rw [value18, value19, value20, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (77 : Vertex) (78 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 25 = false := by
  rw [value21, value22, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (81 : Vertex) (82 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 145 = true ∨ valuation q 22 = true ∨ valuation q 25 = true := by
  rw [value21, value22, value25, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(81 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (82 : Vertex) [(81 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 145 = true ∨ valuation q 22 = true ∨ valuation q 23 = true := by
  rw [value21, value22, value23, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(81 : Vertex), (82 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (84 : Vertex) [(81 : Vertex), (82 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 12 = false ∨ valuation q 21 = false ∨ valuation q 58 = false := by
  rw [value12, value21, value22, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (80 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 146 = true ∨ valuation q 21 = true ∨ valuation q 24 = true ∨ valuation q 58 = true := by
  rw [value21, value22, value24, value58, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(80 : Vertex), (83 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (65 : Vertex) [(80 : Vertex), (83 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 146 = true ∨ valuation q 12 = true ∨ valuation q 24 = true ∨ valuation q 58 = true := by
  rw [value12, value22, value24, value58, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(65 : Vertex), (83 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (80 : Vertex) [(65 : Vertex), (83 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 146 = true ∨ valuation q 12 = true ∨ valuation q 21 = true ∨ valuation q 58 = true := by
  rw [value12, value21, value22, value58, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(65 : Vertex), (80 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (83 : Vertex) [(65 : Vertex), (80 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 23 = true := by
  rw [value23, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (82 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = true ∨ valuation q 24 = true ∨ valuation q 26 = true := by
  rw [value21, value23, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ∈ [(80 : Vertex), (83 : Vertex), (90 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (82 : Vertex) [(80 : Vertex), (83 : Vertex), (90 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 147 = true ∨ valuation q 24 = true ∨ valuation q 26 = true := by
  rw [value23, value24, value26, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(83 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (80 : Vertex) [(83 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 147 = true ∨ valuation q 21 = true ∨ valuation q 24 = true := by
  rw [value21, value23, value24, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(80 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (90 : Vertex) [(80 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 22 = false := by
  rw [value6, value13, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (67 : Vertex) (81 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 23 = false := by
  rw [value6, value13, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (67 : Vertex) (82 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 59 = false := by
  rw [value6, value13, value24, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (67 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 76 = false := by
  rw [value6, value13, value24, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (67 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value6, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (81 : Vertex) (82 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 22 = false ∨ valuation q 59 = false := by
  rw [value6, value22, value24, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (81 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 22 = false ∨ valuation q 76 = false := by
  rw [value6, value22, value24, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (81 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 23 = false ∨ valuation q 59 = false := by
  rw [value6, value23, value24, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (82 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 23 = false ∨ valuation q 76 = false := by
  rw [value6, value23, value24, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (82 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 59 = false ∨ valuation q 76 = false := by
  rw [value6, value24, value59, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (211 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E105.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112105
