import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 138 = true ∨ valuation q 19 = true := by
  rw [value18, value19, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (97 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(99 : Vertex)] := by decide
  have hg := other_cover q (97 : Vertex) (96 : Vertex) [(99 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 138 = true ∨ valuation q 17 = true := by
  rw [value17, value18, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (97 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(96 : Vertex)] := by decide
  have hg := other_cover q (97 : Vertex) (99 : Vertex) [(96 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 26 = false := by
  rw [value18, value19, value20, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (97 : Vertex) (103 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value18, value20, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (99 : Vertex) (97 : Vertex) (103 : Vertex) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 139 = true ∨ valuation q 20 = true ∨ valuation q 26 = true := by
  rw [value19, value20, value26, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (99 : Vertex) w → w ∈ region → w ≠ (97 : Vertex) → w ∈ [(103 : Vertex), (115 : Vertex)] := by decide
  have hg := other_cover q (99 : Vertex) (97 : Vertex) [(103 : Vertex), (115 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 139 = true ∨ valuation q 18 = true ∨ valuation q 26 = true := by
  rw [value18, value19, value26, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (99 : Vertex) w → w ∈ region → w ≠ (103 : Vertex) → w ∈ [(97 : Vertex), (115 : Vertex)] := by decide
  have hg := other_cover q (99 : Vertex) (103 : Vertex) [(97 : Vertex), (115 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 140 = true ∨ valuation q 23 = true := by
  rw [value20, value23, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(111 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (99 : Vertex) [(111 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 140 = true ∨ valuation q 19 = true := by
  rw [value19, value20, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (111 : Vertex) → w ∈ [(99 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (111 : Vertex) [(99 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 4 = false ∨ valuation q 17 = false ∨ valuation q 79 = false := by
  rw [value4, value17, value21, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (40 : Vertex) (96 : Vertex) (360 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 17 = false ∨ valuation q 29 = false ∨ valuation q 79 = false := by
  rw [value17, value21, value29, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (96 : Vertex) (120 : Vertex) (360 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 141 = true ∨ valuation q 4 = true ∨ valuation q 29 = true ∨ valuation q 79 = true := by
  rw [value4, value21, value29, value79, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(40 : Vertex), (120 : Vertex), (360 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (96 : Vertex) [(40 : Vertex), (120 : Vertex), (360 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 141 = true ∨ valuation q 4 = true ∨ valuation q 17 = true ∨ valuation q 29 = true := by
  rw [value4, value17, value21, value29, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(40 : Vertex), (96 : Vertex), (120 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (360 : Vertex) [(40 : Vertex), (96 : Vertex), (120 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 142 = true ∨ valuation q 33 = true := by
  rw [value22, value33, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (111 : Vertex) → w ∈ [(125 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (111 : Vertex) [(125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 142 = true ∨ valuation q 23 = true := by
  rw [value22, value23, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(111 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (125 : Vertex) [(111 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 23 = true := by
  rw [value23, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (111 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 20 = true ∨ valuation q 22 = true := by
  rw [value20, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ∈ [(103 : Vertex), (109 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (111 : Vertex) [(103 : Vertex), (109 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 143 = true ∨ valuation q 22 = true := by
  rw [value22, value23, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (103 : Vertex) → w ∈ [(109 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (103 : Vertex) [(109 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 143 = true ∨ valuation q 20 = true := by
  rw [value20, value23, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(103 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (109 : Vertex) [(103 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 25 = false := by
  rw [value9, value17, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (96 : Vertex) (114 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 27 = false := by
  rw [value9, value17, value24, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (96 : Vertex) (116 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 66 = false := by
  rw [value9, value17, value24, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (96 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 9 = false ∨ valuation q 25 = false ∨ valuation q 66 = false := by
  rw [value9, value24, value25, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (114 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 27 = false := by
  rw [value17, value24, value25, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (96 : Vertex) (114 : Vertex) (116 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 17 = false ∨ valuation q 27 = false ∨ valuation q 29 = false := by
  rw [value17, value24, value27, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (96 : Vertex) (116 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 25 = true := by
  rw [value25, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (114 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value24, value25, value26, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (112 : Vertex) (115 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 30 = false := by
  rw [value24, value25, value26, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (112 : Vertex) (115 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 24 = false ∨ valuation q 28 = false ∨ valuation q 30 = false := by
  rw [value24, value25, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (112 : Vertex) (118 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 30 = false := by
  rw [value25, value26, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (115 : Vertex) (118 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 145 = true ∨ valuation q 24 = true ∨ valuation q 26 = true ∨ valuation q 30 = true := by
  rw [value24, value25, value26, value30, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (114 : Vertex) w → w ∈ region → w ≠ (118 : Vertex) → w ∈ [(112 : Vertex), (115 : Vertex), (122 : Vertex)] := by decide
  have hg := other_cover q (114 : Vertex) (118 : Vertex) [(112 : Vertex), (115 : Vertex), (122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 145 = true ∨ valuation q 24 = true ∨ valuation q 26 = true ∨ valuation q 28 = true := by
  rw [value24, value25, value26, value28, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (114 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(112 : Vertex), (115 : Vertex), (118 : Vertex)] := by decide
  have hg := other_cover q (114 : Vertex) (122 : Vertex) [(112 : Vertex), (115 : Vertex), (118 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 25 = false := by
  rw [value10, value19, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (115 : Vertex) (51 : Vertex) (99 : Vertex) (114 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E004.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112004
