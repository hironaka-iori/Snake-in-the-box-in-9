import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 20 = true ∨ valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 34 = true := by
  rw [value20, value24, value25, value27, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ∈ [(66 : Vertex), (75 : Vertex), (78 : Vertex), (90 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (74 : Vertex) [(66 : Vertex), (75 : Vertex), (78 : Vertex), (90 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 134 = true ∨ valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 34 = true := by
  rw [value24, value25, value27, value34, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(75 : Vertex), (78 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (66 : Vertex) [(75 : Vertex), (78 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 134 = true ∨ valuation q 20 = true ∨ valuation q 25 = true ∨ valuation q 34 = true := by
  rw [value20, value24, value25, value34, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(66 : Vertex), (75 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (78 : Vertex) [(66 : Vertex), (75 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value7, value21, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (67 : Vertex) (74 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 21 = false ∨ valuation q 35 = false := by
  rw [value7, value21, value25, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (67 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 24 = false ∨ valuation q 35 = false := by
  rw [value7, value24, value25, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (74 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 24 = false ∨ valuation q 83 = false := by
  rw [value7, value24, value25, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (74 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 35 = false := by
  rw [value21, value24, value25, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (74 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 35 = false ∨ valuation q 83 = false := by
  rw [value21, value25, value35, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (91 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 24 = false ∨ valuation q 35 = false ∨ valuation q 83 = false := by
  rw [value24, value25, value35, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (74 : Vertex) (91 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 26 = true := by
  rw [value26, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (76 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 136 = true ∨ valuation q 27 = true := by
  rw [value26, value27, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(78 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (68 : Vertex) [(78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 136 = true ∨ valuation q 22 = true := by
  rw [value22, value26, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(68 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (78 : Vertex) [(68 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 137 = true ∨ valuation q 26 = true := by
  rw [value26, value27, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(76 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (74 : Vertex) [(76 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 137 = true ∨ valuation q 24 = true := by
  rw [value24, value27, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(74 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (76 : Vertex) [(74 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 10 = false ∨ valuation q 29 = false ∨ valuation q 32 = false := by
  rw [value10, value28, value29, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (16 : Vertex) (84 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 32 = false ∨ valuation q 54 = false := by
  rw [value28, value29, value32, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (84 : Vertex) (88 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 22 = false ∨ valuation q 28 = false ∨ valuation q 30 = false := by
  rw [value22, value28, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (80 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 22 = false ∨ valuation q 28 = false ∨ valuation q 89 = false := by
  rw [value22, value28, value29, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (80 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 89 = false := by
  rw [value22, value29, value30, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (85 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 139 = true ∨ valuation q 22 = true ∨ valuation q 28 = true ∨ valuation q 89 = true := by
  rw [value22, value28, value29, value89, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(68 : Vertex), (80 : Vertex), (340 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (85 : Vertex) [(68 : Vertex), (80 : Vertex), (340 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 23 = false ∨ valuation q 29 = false ∨ valuation q 31 = false := by
  rw [value23, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (85 : Vertex) (69 : Vertex) (84 : Vertex) (87 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 140 = true ∨ valuation q 29 = true ∨ valuation q 31 = true := by
  rw [value29, value30, value31, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(84 : Vertex), (87 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (69 : Vertex) [(84 : Vertex), (87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 140 = true ∨ valuation q 23 = true ∨ valuation q 29 = true := by
  rw [value23, value29, value30, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(69 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (87 : Vertex) [(69 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 30 = true ∨ valuation q 36 = true := by
  rw [value30, value31, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ∈ [(85 : Vertex), (95 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (87 : Vertex) [(85 : Vertex), (95 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 141 = true ∨ valuation q 36 = true := by
  rw [value31, value36, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(95 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (85 : Vertex) [(95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 141 = true ∨ valuation q 30 = true := by
  rw [value30, value31, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(85 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (95 : Vertex) [(85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 142 = true ∨ valuation q 28 = true ∨ valuation q 33 = true ∨ valuation q 34 = true := by
  rw [value28, value32, value33, value34, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(80 : Vertex), (89 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (24 : Vertex) [(80 : Vertex), (89 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 142 = true ∨ valuation q 15 = true ∨ valuation q 28 = true ∨ valuation q 34 = true := by
  rw [value15, value28, value32, value34, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(24 : Vertex), (80 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (89 : Vertex) [(24 : Vertex), (80 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 142 = true ∨ valuation q 15 = true ∨ valuation q 28 = true ∨ valuation q 33 = true := by
  rw [value15, value28, value32, value33, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(24 : Vertex), (80 : Vertex), (89 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (90 : Vertex) [(24 : Vertex), (80 : Vertex), (89 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 143 = true ∨ valuation q 35 = true := by
  rw [value33, value35, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(91 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (88 : Vertex) [(91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 24 = false ∨ valuation q 32 = false ∨ valuation q 35 = false := by
  rw [value24, value32, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (88 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E183.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112183
