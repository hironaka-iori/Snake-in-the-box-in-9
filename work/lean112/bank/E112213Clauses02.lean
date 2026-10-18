import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 21 = false ∨ valuation q 27 = false ∨ valuation q 56 = false := by
  rw [value15, value21, value27, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (72 : Vertex) (80 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 21 = false ∨ valuation q 27 = false ∨ valuation q 74 = false := by
  rw [value15, value21, value27, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (72 : Vertex) (80 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 21 = false ∨ valuation q 56 = false ∨ valuation q 74 = false := by
  rw [value15, value21, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (72 : Vertex) (192 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 27 = false ∨ valuation q 56 = false ∨ valuation q 74 = false := by
  rw [value15, value27, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (80 : Vertex) (192 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 2 = false ∨ valuation q 18 = false ∨ valuation q 19 = false := by
  rw [value2, value16, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (1 : Vertex) (67 : Vertex) (69 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 2 = false ∨ valuation q 18 = false ∨ valuation q 57 = false := by
  rw [value2, value16, value18, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (1 : Vertex) (67 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 2 = false ∨ valuation q 19 = false ∨ valuation q 28 = false := by
  rw [value2, value16, value19, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (1 : Vertex) (69 : Vertex) (81 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 2 = false ∨ valuation q 19 = false ∨ valuation q 57 = false := by
  rw [value2, value16, value19, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (1 : Vertex) (69 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 2 = false ∨ valuation q 28 = false ∨ valuation q 57 = false := by
  rw [value2, value16, value28, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (1 : Vertex) (81 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 2 = false ∨ valuation q 28 = false ∨ valuation q 75 = false := by
  rw [value2, value16, value28, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (1 : Vertex) (81 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 2 = false ∨ valuation q 57 = false ∨ valuation q 75 = false := by
  rw [value2, value16, value57, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (1 : Vertex) (193 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 57 = false := by
  rw [value16, value18, value19, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (67 : Vertex) (69 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 29 = false := by
  rw [value15, value17, value18, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (66 : Vertex) (64 : Vertex) (67 : Vertex) (82 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 134 = true ∨ valuation q 18 = true ∨ valuation q 29 = true := by
  rw [value17, value18, value29, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (64 : Vertex) → w ∈ [(67 : Vertex), (82 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (64 : Vertex) [(67 : Vertex), (82 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 134 = true ∨ valuation q 15 = true ∨ valuation q 29 = true := by
  rw [value15, value17, value29, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (67 : Vertex) → w ∈ [(64 : Vertex), (82 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (67 : Vertex) [(64 : Vertex), (82 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 134 = true ∨ valuation q 15 = true ∨ valuation q 18 = true := by
  rw [value15, value17, value18, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(64 : Vertex), (67 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (82 : Vertex) [(64 : Vertex), (67 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 20 = false := by
  rw [value16, value17, value18, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (65 : Vertex) (66 : Vertex) (71 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 22 = false := by
  rw [value16, value17, value18, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (65 : Vertex) (66 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 30 = false := by
  rw [value16, value17, value18, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (65 : Vertex) (66 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 20 = false ∨ valuation q 22 = false := by
  rw [value16, value18, value20, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (65 : Vertex) (71 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 20 = false ∨ valuation q 30 = false := by
  rw [value16, value18, value20, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (65 : Vertex) (71 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 22 = false ∨ valuation q 30 = false := by
  rw [value16, value18, value22, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (65 : Vertex) (75 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 22 = false := by
  rw [value17, value18, value20, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (66 : Vertex) (71 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 30 = false := by
  rw [value17, value18, value20, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (66 : Vertex) (71 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 17 = false ∨ valuation q 22 = false ∨ valuation q 30 = false := by
  rw [value17, value18, value22, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (66 : Vertex) (75 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 30 = false := by
  rw [value18, value20, value22, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (71 : Vertex) (75 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 135 = true ∨ valuation q 16 = true ∨ valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 30 = true := by
  rw [value16, value18, value20, value22, value30, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(65 : Vertex), (71 : Vertex), (75 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (66 : Vertex) [(65 : Vertex), (71 : Vertex), (75 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 135 = true ∨ valuation q 16 = true ∨ valuation q 17 = true ∨ valuation q 20 = true ∨ valuation q 22 = true := by
  rw [value16, value17, value18, value20, value22, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(65 : Vertex), (66 : Vertex), (71 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (83 : Vertex) [(65 : Vertex), (66 : Vertex), (71 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 16 = false ∨ valuation q 20 = false ∨ valuation q 24 = false := by
  rw [value16, value19, value20, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (65 : Vertex) (71 : Vertex) (77 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 136 = true ∨ valuation q 16 = true ∨ valuation q 20 = true := by
  rw [value16, value19, value20, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (77 : Vertex) → w ∈ [(65 : Vertex), (71 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (77 : Vertex) [(65 : Vertex), (71 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 137 = true ∨ valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 60 = true ∨ valuation q 77 = true := by
  rw [value18, value19, value20, value60, value77, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (71 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(67 : Vertex), (69 : Vertex), (199 : Vertex), (327 : Vertex)] := by decide
  have hg := other_cover q (71 : Vertex) (79 : Vertex) [(67 : Vertex), (69 : Vertex), (199 : Vertex), (327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 137 = true ∨ valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 26 = true ∨ valuation q 60 = true := by
  rw [value18, value19, value20, value26, value60, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (71 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(67 : Vertex), (69 : Vertex), (79 : Vertex), (199 : Vertex)] := by decide
  have hg := other_cover q (71 : Vertex) (327 : Vertex) [(67 : Vertex), (69 : Vertex), (79 : Vertex), (199 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E213.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112213
