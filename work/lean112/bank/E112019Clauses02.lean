import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 135 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 22 = true := by
  rw [value12, value13, value14, value22, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(75 : Vertex), (77 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (71 : Vertex) [(75 : Vertex), (77 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 135 = true ∨ valuation q 10 = true ∨ valuation q 12 = true ∨ valuation q 22 = true := by
  rw [value10, value12, value14, value22, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (77 : Vertex) → w ∈ [(71 : Vertex), (75 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (77 : Vertex) [(71 : Vertex), (75 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 135 = true ∨ valuation q 10 = true ∨ valuation q 12 = true ∨ valuation q 13 = true := by
  rw [value10, value12, value13, value14, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(71 : Vertex), (75 : Vertex), (77 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (95 : Vertex) [(71 : Vertex), (75 : Vertex), (77 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 19 = false := by
  rw [value15, value16, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (81 : Vertex) (84 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 136 = true ∨ valuation q 18 = true ∨ valuation q 19 = true := by
  rw [value15, value18, value19, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (81 : Vertex) → w ∈ [(84 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (81 : Vertex) [(84 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 136 = true ∨ valuation q 16 = true ∨ valuation q 18 = true := by
  rw [value15, value16, value18, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(81 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (88 : Vertex) [(81 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 16 = true := by
  rw [value16, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (81 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 15 = true ∨ valuation q 17 = true := by
  rw [value15, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ∈ [(80 : Vertex), (83 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (81 : Vertex) [(80 : Vertex), (83 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 137 = true ∨ valuation q 17 = true := by
  rw [value16, value17, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(83 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (80 : Vertex) [(83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 137 = true ∨ valuation q 15 = true := by
  rw [value15, value16, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(80 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (83 : Vertex) [(80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 138 = true ∨ valuation q 16 = true := by
  rw [value16, value17, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (67 : Vertex) → w ∈ [(81 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (67 : Vertex) [(81 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 138 = true ∨ valuation q 7 = true := by
  rw [value7, value17, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (81 : Vertex) → w ∈ [(67 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (81 : Vertex) [(67 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 18 = true := by
  rw [value18, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (84 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 20 = false := by
  rw [value8, value15, value18, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (80 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 50 = false := by
  rw [value8, value15, value18, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (80 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 139 = true ∨ valuation q 8 = true ∨ valuation q 20 = true ∨ valuation q 50 = true := by
  rw [value8, value18, value20, value50, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(68 : Vertex), (92 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (80 : Vertex) [(68 : Vertex), (92 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 15 = false ∨ valuation q 20 = false ∨ valuation q 74 = false := by
  rw [value15, value19, value20, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (80 : Vertex) (92 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 140 = true ∨ valuation q 20 = true ∨ valuation q 74 = true := by
  rw [value19, value20, value74, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(92 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (80 : Vertex) [(92 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 140 = true ∨ valuation q 15 = true ∨ valuation q 74 = true := by
  rw [value15, value19, value74, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(80 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (92 : Vertex) [(80 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 140 = true ∨ valuation q 15 = true ∨ valuation q 20 = true := by
  rw [value15, value19, value20, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(80 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (344 : Vertex) [(80 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 21 = false := by
  rw [value18, value19, value20, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (84 : Vertex) (88 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 141 = true ∨ valuation q 18 = true ∨ valuation q 21 = true := by
  rw [value18, value20, value21, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (92 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(84 : Vertex), (94 : Vertex)] := by decide
  have hg := other_cover q (92 : Vertex) (88 : Vertex) [(84 : Vertex), (94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 141 = true ∨ valuation q 18 = true ∨ valuation q 19 = true := by
  rw [value18, value19, value20, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (92 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(84 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (92 : Vertex) (94 : Vertex) [(84 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 21 = true := by
  rw [value21, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (94 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 20 = true ∨ valuation q 22 = true := by
  rw [value20, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ∈ [(92 : Vertex), (95 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (94 : Vertex) [(92 : Vertex), (95 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 142 = true ∨ valuation q 22 = true := by
  rw [value21, value22, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(95 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (92 : Vertex) [(95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 142 = true ∨ valuation q 20 = true := by
  rw [value20, value21, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(92 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (95 : Vertex) [(92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 143 = true ∨ valuation q 21 = true := by
  rw [value21, value22, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(94 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (79 : Vertex) [(94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 143 = true ∨ valuation q 14 = true := by
  rw [value14, value22, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(79 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (94 : Vertex) [(79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 28 = false ∨ valuation q 81 = false := by
  rw [value23, value24, value28, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (138 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 144 = true ∨ valuation q 28 = true ∨ valuation q 81 = true := by
  rw [value23, value28, value81, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(138 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (131 : Vertex) [(138 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 144 = true ∨ valuation q 24 = true ∨ valuation q 28 = true := by
  rw [value23, value24, value28, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(131 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (386 : Vertex) [(131 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E019.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112019
