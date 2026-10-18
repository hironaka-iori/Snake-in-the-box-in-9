import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 13 = true ∨ valuation q 31 = true := by
  rw [value13, value19, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (58 : Vertex) w → w ∈ region → w ∈ [(42 : Vertex), (122 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (58 : Vertex) [(42 : Vertex), (122 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 13 = false ∨ valuation q 31 = false := by
  rw [value13, value31, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (58 : Vertex) (42 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 19 = true := by
  rw [value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 123 = true := by
  rw [value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change BallClauseLogic.Endpoint q head
  exact (endpoint_iff q head).mpr (Or.inl h.head_fixed.symm)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 8 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value8, value20, value21, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (96 : Vertex) (32 : Vertex) (97 : Vertex) (104 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 124 = true ∨ valuation q 8 = true ∨ valuation q 24 = true := by
  rw [value8, value20, value24, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (97 : Vertex) → w ∈ [(32 : Vertex), (104 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (97 : Vertex) [(32 : Vertex), (104 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 125 = true ∨ valuation q 27 = true := by
  rw [value21, value27, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (97 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(113 : Vertex)] := by decide
  have hg := other_cover q (97 : Vertex) (96 : Vertex) [(113 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 125 = true ∨ valuation q 20 = true := by
  rw [value20, value21, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (97 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(96 : Vertex)] := by decide
  have hg := other_cover q (97 : Vertex) (113 : Vertex) [(96 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 11 = false ∨ valuation q 23 = false ∨ valuation q 30 = false := by
  rw [value11, value22, value23, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (38 : Vertex) (103 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 12 = false ∨ valuation q 22 = false ∨ valuation q 26 = false := by
  rw [value12, value22, value23, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (103 : Vertex) (39 : Vertex) (102 : Vertex) (111 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 127 = true ∨ valuation q 12 = true ∨ valuation q 22 = true := by
  rw [value12, value22, value23, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (111 : Vertex) → w ∈ [(39 : Vertex), (102 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (111 : Vertex) [(39 : Vertex), (102 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 128 = true ∨ valuation q 64 = true := by
  rw [value24, value64, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(232 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (96 : Vertex) [(232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 128 = true ∨ valuation q 20 = true := by
  rw [value20, value24, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(96 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (232 : Vertex) [(96 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 129 = true ∨ valuation q 33 = true := by
  rw [value25, value33, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (111 : Vertex) → w ∈ [(125 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (111 : Vertex) [(125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 129 = true ∨ valuation q 26 = true := by
  rw [value25, value26, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(111 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (125 : Vertex) [(111 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 130 = true ∨ valuation q 23 = true := by
  rw [value23, value26, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(103 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (109 : Vertex) [(103 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 131 = true ∨ valuation q 29 = true := by
  rw [value27, value29, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ≠ (97 : Vertex) → w ∈ [(115 : Vertex)] := by decide
  have hg := other_cover q (113 : Vertex) (97 : Vertex) [(115 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 131 = true ∨ valuation q 21 = true := by
  rw [value21, value27, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ≠ (115 : Vertex) → w ∈ [(97 : Vertex)] := by decide
  have hg := other_cover q (113 : Vertex) (115 : Vertex) [(97 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value28, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (115 : Vertex) (118 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 132 = true ∨ valuation q 30 = true ∨ valuation q 31 = true := by
  rw [value28, value30, value31, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (114 : Vertex) w → w ∈ region → w ≠ (115 : Vertex) → w ∈ [(118 : Vertex), (122 : Vertex)] := by decide
  have hg := other_cover q (114 : Vertex) (115 : Vertex) [(118 : Vertex), (122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 132 = true ∨ valuation q 29 = true ∨ valuation q 31 = true := by
  rw [value28, value29, value31, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (114 : Vertex) w → w ∈ region → w ≠ (118 : Vertex) → w ∈ [(115 : Vertex), (122 : Vertex)] := by decide
  have hg := other_cover q (114 : Vertex) (118 : Vertex) [(115 : Vertex), (122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 27 = true ∨ valuation q 28 = true := by
  rw [value27, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ∈ [(113 : Vertex), (114 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (115 : Vertex) [(113 : Vertex), (114 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 133 = true ∨ valuation q 28 = true := by
  rw [value28, value29, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(114 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (113 : Vertex) [(114 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 133 = true ∨ valuation q 27 = true := by
  rw [value27, value29, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(113 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (114 : Vertex) [(113 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 22 = false ∨ valuation q 28 = false ∨ valuation q 34 = false := by
  rw [value22, value28, value30, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (118 : Vertex) (102 : Vertex) (114 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 134 = true ∨ valuation q 28 = true ∨ valuation q 34 = true := by
  rw [value28, value30, value34, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (102 : Vertex) → w ∈ [(114 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (102 : Vertex) [(114 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 134 = true ∨ valuation q 22 = true ∨ valuation q 34 = true := by
  rw [value22, value30, value34, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(102 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (114 : Vertex) [(102 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 134 = true ∨ valuation q 22 = true ∨ valuation q 28 = true := by
  rw [value22, value28, value30, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(102 : Vertex), (114 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (126 : Vertex) [(102 : Vertex), (114 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 34 = false := by
  rw [value19, value28, value31, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (122 : Vertex) (58 : Vertex) (114 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 135 = true ∨ valuation q 28 = true ∨ valuation q 34 = true := by
  rw [value28, value31, value34, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(114 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (58 : Vertex) [(114 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 136 = true ∨ valuation q 34 = true := by
  rw [value32, value34, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(126 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (125 : Vertex) [(126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 136 = true ∨ valuation q 33 = true := by
  rw [value32, value33, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(125 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (126 : Vertex) [(125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E145.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112145
